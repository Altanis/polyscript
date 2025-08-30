use std::collections::{HashMap, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

use inkwell::context::Context;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple};
use inkwell::OptimizationLevel;

use crate::backend::codegen::codegen::CodeGen;
use crate::backend::optimizations::{capture_analysis, escape_analysis};
use crate::frontend::semantics::analyzer::{ScopeId, SemanticAnalyzer, TypeSymbolId, ValueSymbolId};
use crate::frontend::syntax::ast::{AstNode, AstNodeKind};
use crate::frontend::syntax::lexer::Lexer;
use crate::frontend::syntax::parser::Parser;
use crate::mir::builder::MIRBuilder;
use crate::mir::ir_node::MIRNode;
use crate::utils::error::{BoxedError, ErrorKind};
use crate::utils::kind::Token;

pub const DEBUG: bool = true;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EmitType {
    Asm,
    Obj,
    LLIR,
    Executable,
}

#[derive(Debug)]
pub struct CompilerConfig {
    pub entry_file: String,
    pub opt_level: OptimizationLevel,
    pub target_triple: String,
    pub cpu: String,
    pub emit_type: EmitType,
    pub output_file: PathBuf,
    pub debug_symbols: bool,
    pub features: String,
    pub linker: String
}

pub struct Module {
    pub path: PathBuf,
    pub ast: AstNode,
    pub lined_source: Rc<Vec<String>>,
    pub scope_id: ScopeId,
    pub exports: HashMap<String, (Option<ValueSymbolId>, Option<TypeSymbolId>)>,
}

pub struct Compiler {
    config: CompilerConfig,
    analyzer: SemanticAnalyzer,
    modules: HashMap<PathBuf, Module>,
}

impl Compiler {
    pub fn new(config: CompilerConfig) -> Compiler {
        Compiler {
            config,
            analyzer: SemanticAnalyzer::new(Rc::new(vec![])),
            modules: HashMap::new(),
        }
    }

    pub fn run(&mut self) {
        let mut file_queue: VecDeque<PathBuf> = VecDeque::new();
        let entry_path = fs::canonicalize(&self.config.entry_file).expect("Failed to find entry file.");
        file_queue.push_back(entry_path.clone());

        let mut all_modules_paths = vec![entry_path.clone()];

        while let Some(current_path) = file_queue.pop_front() {
            if self.modules.contains_key(&current_path) {
                continue;
            }

            let source_code = fs::read_to_string(&current_path).unwrap_or_else(|_| panic!("Could not read source file: {:?}", current_path));
            let (lined_source, tokens) = self.generate_tokens(source_code);
            let mut ast = self.parse_tokens(lined_source.clone(), tokens.clone());

            if let AstNodeKind::Program(stmts) = &ast.kind {
                for stmt in stmts {
                    if let AstNodeKind::ImportStatement { file_path: rel_path_str, .. } = &stmt.kind {
                        let mut dep_path = current_path.parent().unwrap().to_path_buf();
                        dep_path.push(rel_path_str);
                        let canonical_dep_path = fs::canonicalize(&dep_path)
                            .unwrap_or_else(|_| panic!("Failed to resolve import path: {:?}", dep_path));
                        
                        if !all_modules_paths.contains(&canonical_dep_path) {
                            file_queue.push_back(canonical_dep_path.clone());
                            all_modules_paths.push(canonical_dep_path);
                        }
                    }
                }
            }
            
            self.analyzer.symbol_table.current_scope_id = 0;
            let module_scope_id = self.analyzer.symbol_table.enter_scope(crate::frontend::semantics::analyzer::ScopeKind::Block);
            ast.scope_id = Some(module_scope_id);

            let module = Module {
                path: current_path.clone(),
                ast,
                lined_source: Rc::new(lined_source),
                scope_id: module_scope_id,
                exports: HashMap::new(),
            };

            self.modules.insert(current_path, module);
        }

        for path in &all_modules_paths {
            let module = self.modules.get_mut(path).unwrap();
            self.analyzer.symbol_table.current_scope_id = module.scope_id;
            
            let errors = self.analyzer.symbol_collector_pass(&mut module.ast);
            if !errors.is_empty() {
                println!("{} errors emitted... printing:", errors.len());
                for err in errors {
                    eprintln!("{}", err);
                }
            }
        }

        for path in &all_modules_paths {
            self.resolve_exports_for_module(path).unwrap();
        }

        for path in &all_modules_paths {
            self.link_imports_for_module(path).unwrap();
        }
        
        for path in &all_modules_paths {
            let module = self.modules.get_mut(path).unwrap();
            self.analyzer.symbol_table.current_scope_id = module.scope_id;
            self.analyzer.set_source(module.lined_source.clone());

            if let Err(errs) = self.analyzer.analyze(&mut module.ast) {
                println!("{} errors emitted in {:?}... printing:", errs.len(), path);
                for err in errs { eprintln!("{}", err); }
                std::process::exit(1);
            }
        }

        let (_, mut mir_program) = self.lower_ast_to_mir(entry_path);
        self.optimize(&mut mir_program);
        self.compile_mir(mir_program);
    }

    fn resolve_exports_for_module(&mut self, path: &Path) -> Result<(), BoxedError> {
        let module = self.modules.get(path).unwrap();
        self.analyzer.symbol_table.current_scope_id = module.scope_id;
        
        let mut exports = HashMap::new();
        if let AstNodeKind::Program(stmts) = &module.ast.kind {
            for stmt in stmts {
                if let AstNodeKind::ExportStatement { identifiers } = &stmt.kind {
                    for ident_node in identifiers {
                        let name = ident_node.get_name().unwrap();
                        let value_sym = self.analyzer.symbol_table.find_value_symbol_in_scope(&name, module.scope_id);
                        let type_sym = self.analyzer.symbol_table.find_type_symbol_in_scope(&name, module.scope_id);

                        if value_sym.is_none() && type_sym.is_none() {
                             return Err(self.analyzer.create_error(ErrorKind::UnknownIdentifier(name), ident_node.span, &[ident_node.span]));
                        }
                        
                        exports.insert(name, (value_sym.map(|s| s.id), type_sym.map(|s| s.id)));
                    }
                }
            }
        }
        
        self.modules.get_mut(path).unwrap().exports = exports;

        Ok(())
    }

    fn link_imports_for_module(&mut self, path: &Path) -> Result<(), BoxedError> {
        let mut dependencies = Vec::new();
        let module = self.modules.get(path).unwrap();
        if let AstNodeKind::Program(stmts) = &module.ast.kind {
            for stmt in stmts {
                if let AstNodeKind::ImportStatement { file_path, identifiers, .. } = &stmt.kind {
                    let mut dep_path = path.parent().unwrap().to_path_buf();
                    dep_path.push(file_path);
                    let canonical_dep_path = fs::canonicalize(&dep_path).unwrap();
                    dependencies.push((canonical_dep_path, identifiers.clone()));
                }
            }
        }

        for (dep_path, identifiers) in dependencies {
            let importing_module = self.modules.get(path).unwrap();
            self.analyzer.symbol_table.current_scope_id = importing_module.scope_id;
            
            let imported_module = self.modules.get(&dep_path).unwrap();
            
            for ident_node in &identifiers {
                let name = ident_node.get_name().unwrap();
                let (exported_value_id, exported_type_id) = imported_module.exports.get(&name)
                    .ok_or_else(|| self.analyzer.create_error(
                        ErrorKind::MemberNotFound(name.clone(), format!("module {:?}", imported_module.path)), 
                        ident_node.span, 
                        &[ident_node.span])
                    )?;
                
                if let Some(val_id) = exported_value_id {
                    let name_id = self.analyzer.symbol_table.value_names.intern(&name);
                    self.analyzer.symbol_table.get_scope_mut(importing_module.scope_id).unwrap().values.insert(name_id, *val_id);
                }

                if let Some(type_id) = exported_type_id {
                    let name_id = self.analyzer.symbol_table.type_names.intern(&name);
                    self.analyzer.symbol_table.get_scope_mut(importing_module.scope_id).unwrap().types.insert(name_id, *type_id);
                }
            }
        }
        Ok(())
    }

    fn generate_tokens(&self, program: String) -> (Vec<String>, Vec<Token>) {
        let mut lexer = Lexer::new(program);
        let tokens = lexer.tokenize();

        if let Err(e) = tokens {
            eprintln!("{}", e);
            std::process::exit(1);
        }

        lexer.extract()
    }

    fn parse_tokens(&self, lined_source: Vec<String>, tokens: Vec<Token>) -> AstNode {
        let mut parser = Parser::new(lined_source, tokens);

        match parser.parse() {
            Err(errs) => {
                println!("{} errors emitted... printing:", errs.len());
                for err in errs {
                    eprintln!("{}", err);
                }

                std::process::exit(1);
            },
            Ok(program) => program
        }
    }

    fn analyze_ast(&self, lined_source: Vec<String>, mut program: AstNode) -> (AstNode, SemanticAnalyzer) {
        let mut analyzer = SemanticAnalyzer::new(Rc::new(lined_source));
        match analyzer.analyze(&mut program) {
            Err(errs) => {
                println!("{} errors emitted... printing:", errs.len());
                for err in errs {
                    eprintln!("{}", err);
                }

                std::process::exit(1);
            },
            Ok(_) => (program, analyzer)
        }
    }

    fn lower_ast_to_mir<'s>(&'s mut self, canonical_entry_path: PathBuf) -> (MIRBuilder<'s>, MIRNode) {
        let entry_module = self.modules.get_mut(&canonical_entry_path).unwrap();
        let mut builder = MIRBuilder::new(&mut self.analyzer);
        let program = builder.build(&mut entry_module.ast);

        (builder, program)
    }

    fn optimize(&mut self, program: &mut MIRNode) {
        let mut errs = vec![];
        errs.extend(escape_analysis::init(program, &mut self.analyzer));
        capture_analysis::init(program, &self.analyzer);

        if !errs.is_empty() {
            println!("{} errors emitted... printing:", errs.len());
            for err in errs {
                eprintln!("{}", err);
            }

            std::process::exit(1);
        }
    }

    fn compile_mir(&self, program: MIRNode) {
        let context = Context::create();
        let module = context.create_module("main_module");
        let builder = context.create_builder();

        Target::initialize_all(&InitializationConfig::default());

        let target_triple = if self.config.target_triple.is_empty() { TargetMachine::get_default_triple() } else { TargetTriple::create(&self.config.target_triple) };
        let cpu = if self.config.cpu.is_empty() { TargetMachine::get_host_cpu_name().to_string() } else { self.config.cpu.clone() };
        let features = if self.config.features.is_empty() { TargetMachine::get_host_cpu_features().to_string() } else { self.config.features.clone() };

        module.set_triple(&target_triple);
        let target = Target::from_triple(&target_triple).expect("Target not found");

        let target_machine = target.create_target_machine(
            &target_triple,
            &cpu,
            &features,
            self.config.opt_level,
            RelocMode::Default,
            CodeModel::Default,
        ).expect("Failed to create target machine");

        module.set_data_layout(&target_machine.get_target_data().get_data_layout());

        if self.config.debug_symbols {
            println!("[WARN] Debug symbols are not supported yet.");
        }

        let mut codegen = CodeGen::new(&context, &builder, &module, &self.analyzer);
        codegen.compile_program(&program);

        if let Some(parent) = self.config.output_file.parent() && !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).expect("Failed to create output directory");
        }

        match self.config.emit_type {
            EmitType::LLIR => {
                module.print_to_file(&self.config.output_file).expect("Couldn't write LLVM IR to file");
            },
            EmitType::Asm => {
                target_machine.write_to_file(&module, FileType::Assembly, &self.config.output_file).expect("Failed to write assembly file");
            },
            EmitType::Obj => {
                target_machine.write_to_file(&module, FileType::Object, &self.config.output_file).expect("Failed to write object file");
            },
            EmitType::Executable => {
                let temp_obj_path = self.config.output_file.with_extension("o");
                target_machine.write_to_file(&module, FileType::Object, &temp_obj_path).expect("Failed to write object file");

                let linker_cmd = {
                    if !self.config.linker.is_empty() {
                        self.config.linker.clone()
                    } else if Command::new("clang").arg("--version").output().is_ok() {
                        "clang".to_string()
                    } else if Command::new("gcc").arg("--version").output().is_ok() {
                        "gcc".to_string()
                    } else {
                        eprintln!("Error: Could not find a linker.");
                        eprintln!("Please specify one with the --linker flag, or make sure 'clang' or 'gcc' is in your PATH.");
                        std::process::exit(1);
                    }
                };

                let status = Command::new(&linker_cmd)
                    .arg(&temp_obj_path)
                    .arg("-o")
                    .arg(&self.config.output_file)
                    .status()
                    .unwrap_or_else(|e| {
                        eprintln!("Failed to run linker '{}': {}", linker_cmd, e);
                        std::process::exit(1);
                    });

                if !status.success() {
                    eprintln!("Linking failed.");
                    std::process::exit(1);
                }

                fs::remove_file(&temp_obj_path).expect("Failed to remove temporary object file");
            }
        }
    }
}