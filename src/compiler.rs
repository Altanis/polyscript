use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

use inkwell::context::Context;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::OptimizationLevel;

use crate::backend::codegen::codegen::CodeGen;
use crate::backend::optimizations::capture_analysis;
use crate::frontend::semantics::analyzer::{ScopeId, ScopeKind, SemanticAnalyzer, TypeSymbolId, ValueSymbolId,};
use crate::frontend::syntax::ast::{AstNode, AstNodeKind};
use crate::frontend::syntax::lexer::Lexer;
use crate::frontend::syntax::parser::Parser;
use crate::mir::builder::MIRBuilder;
use crate::mir::ir_node::MIRNode;
use crate::utils::error::{BoxedError, ErrorKind};
use crate::utils::kind::{Span, Token};

pub const DEBUG: bool = false;
const FILE_EXTENSION: &str = "ps";

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EmitType {
    Asm,
    Obj,
    LLIR,
    Executable,
}

#[derive(Debug)]
pub struct EmitTarget {
    pub kind: EmitType,
    pub path: PathBuf,
}

#[derive(Debug)]
pub struct CompilerConfig {
    pub entry_file: String,
    pub opt_level: OptimizationLevel,
    pub target_triple: String,
    pub cpu: String,
    pub emit_targets: Vec<EmitTarget>,
    pub debug_symbols: bool,
    pub features: String,
    pub linker: String,
    pub stdlib_path: Option<PathBuf>,
}

pub struct Module {
    pub path: PathBuf,
    pub ast: AstNode,
    pub lined_source: Rc<Vec<String>>,
    pub scope_id: ScopeId,
    pub exports: HashMap<String, (Option<ValueSymbolId>, Option<TypeSymbolId>)>,
    pub trusted: bool
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
            analyzer: SemanticAnalyzer::new(Rc::new(vec![]), None),
            modules: HashMap::new(),
        }
    }

    pub fn run(&mut self) {
        let mut file_queue: VecDeque<PathBuf> = VecDeque::new();
        let entry_path = fs::canonicalize(&self.config.entry_file).expect("Failed to find entry file.");

        if !self.config.entry_file.to_lowercase().ends_with(&format!(".{FILE_EXTENSION}")) {
            panic!("The entry file given does not end in extension {FILE_EXTENSION}, please give the compiler a supported file type.");
        }

        file_queue.push_back(entry_path.clone());

        let mut dep_graph: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
        let mut visited_for_discovery: HashSet<PathBuf> = HashSet::new();

        while let Some(current_path) = file_queue.pop_front() {
            let file_path = current_path.as_os_str().to_str().map(|f| f.to_string());
            let trusted = if DEBUG {
                true
            } else {
                self.config.stdlib_path.as_ref().is_some_and(|stdlib_path| current_path.starts_with(stdlib_path))
            };

            if !visited_for_discovery.insert(current_path.clone()) {
                continue;
            }

            let source_code = fs::read_to_string(&current_path).unwrap_or_else(|_| panic!("Could not read source file: {:?}", current_path));
            let (lined_source, tokens) = self.generate_tokens(source_code, file_path.clone(), trusted);
            let lined_source_rc = Rc::new(lined_source);
            self.analyzer.set_source(lined_source_rc.clone(), file_path.clone(), trusted);

            let mut ast = self.parse_tokens((*lined_source_rc).clone(), tokens.clone(), file_path);

            let mut dependencies = vec![];
            if let AstNodeKind::Program(stmts) = &ast.kind {
                for stmt in stmts {
                    if let AstNodeKind::ImportStatement { file_path: rel_path_str, .. } = &stmt.kind {
                        let canonical_dep_path = if rel_path_str == "@intrinsics" {
                            if !trusted {
                                let err = self.analyzer.create_error(
                                    ErrorKind::InvalidImport("@intrinsics".to_string(), "Only standard library modules can import it.".to_string()),
                                    stmt.span,
                                    &[stmt.span]
                                );
                                eprintln!("{}", err);
                                std::process::exit(1);
                            }
                            continue;
                        } else if let Some(stdlib_prefix_path) = rel_path_str.strip_prefix("stdlib/") {
                            if let Some(stdlib_path) = &self.config.stdlib_path {
                                let mut dep_path = stdlib_path.clone();
                                dep_path.push(stdlib_prefix_path);
                                fs::canonicalize(&dep_path).unwrap_or_else(|_| {
                                    panic!("Failed to resolve stdlib import path: {:?}", dep_path)
                                })
                            } else {
                                let err = self.analyzer.create_error(
                                    ErrorKind::InvalidImport(
                                        rel_path_str.clone(),
                                        "Standard library not linked. Use the --stdlib flag.".to_string(),
                                    ),
                                    stmt.span,
                                    &[stmt.span],
                                );
                                eprintln!("{}", err);
                                std::process::exit(1);
                            }
                        } else {
                            let mut dep_path = current_path.parent().unwrap().to_path_buf();
                            dep_path.push(rel_path_str);
                            fs::canonicalize(&dep_path).unwrap_or_else(|_| {
                                panic!("Failed to resolve import path: {:?}", dep_path)
                            })
                        };

                        let file_path = canonical_dep_path.as_os_str().to_str().expect("A file was imported in the source with a name that does not have a valid UTF-8 representation.");
                        if !file_path.to_lowercase().ends_with(&format!(".{FILE_EXTENSION}")) {
                            panic!("A file was imported, {file_path}, that does not end in extension {FILE_EXTENSION}; please give the compiler a supported file type.");
                        }

                        dependencies.push(canonical_dep_path.clone());
                        file_queue.push_back(canonical_dep_path);
                    }
                }
            }

            dep_graph.insert(current_path.clone(), dependencies);

            self.analyzer.symbol_table.current_scope_id = self.analyzer.symbol_table.real_starting_scope;
            let module_scope_id = self.analyzer.symbol_table.enter_scope(ScopeKind::Block);
            ast.scope_id = Some(module_scope_id);

            let module = Module {
                path: current_path.clone(),
                ast,
                lined_source: lined_source_rc,
                scope_id: module_scope_id,
                exports: HashMap::new(),
                trusted
            };

            self.modules.insert(current_path, module);
        }

        let compilation_order = match self.topological_sort(&dep_graph) {
            Ok(order) => order,
            Err(_) => std::process::exit(1),
        };

        for path in &compilation_order {
            let module = self.modules.get_mut(path).unwrap();
            self.analyzer.symbol_table.current_scope_id = module.scope_id;

            let errors = self.analyzer.symbol_collector_pass(&mut module.ast);
            if !errors.is_empty() {
                eprintln!("{} errors emitted in {:?}... printing:", errors.len(), path);
                for err in errors {
                    eprintln!("{}", err);
                }
                std::process::exit(1);
            }
        }

        for path in &compilation_order {
            if let Err(err) = self.resolve_exports_for_module(path) {
                eprintln!("1 error emitted in {:?}... printing:", path);
                eprintln!("{}", err);
                std::process::exit(1);
            }
        }

        for path in &compilation_order {
            if let Err(err) = self.link_imports_for_module(path) {
                eprintln!("1 error emitted in {:?}... printing:", path);
                eprintln!("{}", err);
                std::process::exit(1);
            }
        }

        for path in &compilation_order {
            let file_path = path.as_os_str().to_str().map(|f| f.to_string());
            
            let module = self.modules.get_mut(path).unwrap();
            self.analyzer.symbol_table.current_scope_id = module.scope_id;
            self.analyzer.set_source(module.lined_source.clone(), file_path, module.trusted);

            if let Err(errs) = self.analyzer.analyze(&mut module.ast) {
                eprintln!("{} errors emitted in {:?}... printing:", errs.len(), path);
                for err in errs {
                    eprintln!("{}", err);
                }
                std::process::exit(1);
            }
        }

        let (mir_builder, mut mir_program) = self.lower_ast_to_mir(&compilation_order);

        let mir_builder_fmt = if DEBUG {
            format!("{}", mir_builder)
        } else {
            String::new()
        };
        std::mem::drop(mir_builder);

        self.optimize(&mut mir_program);

        let mut mir_program_fmt = String::new();
        if DEBUG {
            let _ = mir_program.fmt_with_indent(&mut mir_program_fmt, 0, Some(&self.analyzer.symbol_table));
        }

        if DEBUG {
            println!("-- AST --");
            
            let mut ast = String::new();
            for module in self.modules.values() {
                let _ = module.ast.fmt_with_indent(&mut ast, 0, Some(&self.analyzer.symbol_table));
            }

            println!("{}", ast);

            println!("-- SEMANTIC ANALYZER --");
            println!("{}", &self.analyzer);

            println!("-- MIR BUILDER --");
            println!("{}", mir_builder_fmt);

            println!("-- MIR PROGRAM --");
            println!("{}", mir_program_fmt);
        }

        self.compile_mir(mir_program);
    }

    fn topological_sort_util(
        node: &PathBuf,
        dep_graph: &HashMap<PathBuf, Vec<PathBuf>>,
        visited: &mut HashSet<PathBuf>,
        recursion_stack: &mut HashSet<PathBuf>,
        sorted: &mut Vec<PathBuf>,
    ) -> Result<(), ()> {
        visited.insert(node.clone());
        recursion_stack.insert(node.clone());

        if let Some(dependencies) = dep_graph.get(node) {
            for dependency in dependencies {
                if !visited.contains(dependency) {
                    if Self::topological_sort_util(dependency, dep_graph, visited, recursion_stack, sorted).is_err() {
                        return Err(());
                    }
                } else if recursion_stack.contains(dependency) {
                    eprintln!("Error: Circular dependency detected involving module {:?}", dependency);
                    return Err(());
                }
            }
        }

        recursion_stack.remove(node);
        sorted.push(node.clone());
        Ok(())
    }

    fn topological_sort(&self, dep_graph: &HashMap<PathBuf, Vec<PathBuf>>) -> Result<Vec<PathBuf>, ()> {
        let mut visited = HashSet::new();
        let mut recursion_stack = HashSet::new();
        let mut sorted = Vec::new();

        for node in dep_graph.keys() {
            if !visited.contains(node) {
                Self::topological_sort_util(node, dep_graph, &mut visited, &mut recursion_stack, &mut sorted)?;
            }
        }

        Ok(sorted)
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
                            return Err(self.analyzer.create_error(
                                ErrorKind::UnknownIdentifier(name),
                                ident_node.span,
                                &[ident_node.span],
                            ));
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
        let importing_module_scope_id = module.scope_id;

        if let AstNodeKind::Program(stmts) = &module.ast.kind {
            for stmt in stmts {
                if let AstNodeKind::ImportStatement { file_path: rel_path_str, identifiers, .. } = &stmt.kind {
                    if rel_path_str == "@intrinsics" {
                        self.analyzer.symbol_table.current_scope_id = importing_module_scope_id;

                        let intrinsics_scope_id = self.analyzer.symbol_table.intrinsics_scope_id;
                        for ident_node in identifiers {
                            let name = ident_node.get_name().unwrap();
                            let value_sym = self.analyzer.symbol_table.find_value_symbol_in_scope(&name, intrinsics_scope_id).cloned();

                            if value_sym.is_none() {
                                return Err(self.analyzer.create_error(
                                    ErrorKind::InvalidImport(
                                        format!("\"{}\" from @intrinsics", name),
                                        "it is not a valid intrinsic".to_string(),
                                    ),
                                    ident_node.span,
                                    &[ident_node.span],
                                ));
                            }

                            let name_id = self.analyzer.symbol_table.value_names.intern(&name);
                            self.analyzer.symbol_table.get_scope_mut(importing_module_scope_id).unwrap().values.insert(name_id, value_sym.unwrap().id);
                        }
                        
                        continue;
                    }

                    let canonical_dep_path = if let Some(stdlib_prefix_path) = rel_path_str.strip_prefix("stdlib/") {
                        if let Some(stdlib_path) = &self.config.stdlib_path {
                            let mut dep_path = stdlib_path.clone();
                            dep_path.push(stdlib_prefix_path);
                            fs::canonicalize(&dep_path).unwrap_or_else(|_| {
                                panic!("Failed to resolve stdlib import path: {:?}", dep_path)
                            })
                        } else {
                            return Err(self.analyzer.create_error(
                                ErrorKind::InvalidImport(
                                    rel_path_str.clone(),
                                    "Standard library not linked. Use the --stdlib flag.".to_string(),
                                ),
                                stmt.span,
                                &[stmt.span],
                            ));
                        }
                    } else {
                        let mut dep_path = path.parent().unwrap().to_path_buf();
                        dep_path.push(rel_path_str);
                        fs::canonicalize(&dep_path).unwrap_or_else(|_| {
                            panic!("Failed to resolve import path: {:?}", dep_path)
                        })
                    };

                    dependencies.push((canonical_dep_path, identifiers.clone()));
                }
            }
        }

        for (dep_path, identifiers) in dependencies {
            self.analyzer.symbol_table.current_scope_id = importing_module_scope_id;

            let imported_module = self.modules.get(&dep_path).unwrap();

            for ident_node in &identifiers {
                let name = ident_node.get_name().unwrap();
                let (exported_value_id, exported_type_id) =
                    imported_module.exports.get(&name).ok_or_else(|| {
                        self.analyzer.create_error(
                            ErrorKind::MemberNotFound(name.clone(), format!("module {:?}", imported_module.path)),
                            ident_node.span,
                            &[ident_node.span],
                        )
                    })?;

                if let Some(val_id) = exported_value_id {
                    let name_id = self.analyzer.symbol_table.value_names.intern(&name);
                    self.analyzer.symbol_table.get_scope_mut(importing_module_scope_id).unwrap().values.insert(name_id, *val_id);
                }

                if let Some(type_id) = exported_type_id {
                    let name_id = self.analyzer.symbol_table.type_names.intern(&name);
                    self.analyzer.symbol_table.get_scope_mut(importing_module_scope_id).unwrap().types.insert(name_id, *type_id);
                }
            }
        }
        Ok(())
    }

    fn generate_tokens(&self, program: String, file_path: Option<String>, trusted: bool) -> (Vec<String>, Vec<Token>) {
        let mut lexer = Lexer::new(program, file_path.clone(), trusted);
        let tokens = lexer.tokenize();

        if let Err(e) = tokens {
            eprintln!("1 error emitted in {:?}... printing:", file_path);
            eprintln!("{}", e);
            std::process::exit(1);
        }

        lexer.extract()
    }

    fn parse_tokens(&self, lined_source: Vec<String>, tokens: Vec<Token>, file_path: Option<String>) -> AstNode {
        let mut parser = Parser::new(lined_source, tokens, file_path.clone());

        match parser.parse() {
            Err(errs) => {
                eprintln!("{} errors emitted in {:?}... printing:", errs.len(), file_path);
                for err in errs {
                    eprintln!("{}", err);
                }

                std::process::exit(1);
            },
            Ok(program) => program
        }
    }

    fn lower_ast_to_mir<'s>(&'s mut self, compilation_order: &[PathBuf]) -> (MIRBuilder<'s>, MIRNode) {
        let mut builder = MIRBuilder::new(&mut self.analyzer);

        let mut program_stmts = vec![];
        for path in compilation_order {
            let module = self.modules.remove(path).unwrap();
            if let AstNodeKind::Program(stmts) = module.ast.kind {
                program_stmts.extend(stmts);
            }
        }

        let mut program_ast = AstNode {
            kind: AstNodeKind::Program(program_stmts),
            span: Span::default(),
            value_id: None, type_id: None, scope_id: Some(0), id: 0
        };

        let mir_program = builder.build(&mut program_ast);

        (builder, mir_program)
    }

    fn optimize(&mut self, program: &mut MIRNode) {
        capture_analysis::init(program, &self.analyzer);
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

        if let Err(err) = module.verify() {
            panic!("Module verification failed: {}", err);
        }

        let mut obj_file_for_linking: Option<PathBuf> = None;
        let mut executable_target: Option<&EmitTarget> = None;
    
        for target in &self.config.emit_targets {
            if let Some(parent) = target.path.parent() && !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).expect("Failed to create output directory");
            }
    
            match target.kind {
                EmitType::LLIR => module.print_to_file(&target.path).expect("Couldn't write LLVM IR to file"),
                EmitType::Asm => target_machine.write_to_file(&module, FileType::Assembly, &target.path).expect("Failed to write assembly file"),
                EmitType::Obj => {
                    target_machine.write_to_file(&module, FileType::Object, &target.path).expect("Failed to write object file");
                    obj_file_for_linking = Some(target.path.clone());
                },
                EmitType::Executable => {
                    executable_target = Some(target);
                }
            }
        }
    
        if let Some(exec_target) = executable_target {
            let needs_temp_obj = obj_file_for_linking.is_none();
            let obj_path = if needs_temp_obj {
                let temp_path = exec_target.path.with_extension("o");
                target_machine.write_to_file(&module, FileType::Object, &temp_path).expect("Failed to write temporary object file");
                temp_path
            } else {
                obj_file_for_linking.clone().unwrap()
            };
    
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
                .arg(&obj_path)
                .arg("-o")
                .arg(&exec_target.path)
                .status()
                .unwrap_or_else(|e| {
                    eprintln!("Failed to run linker '{}': {}", linker_cmd, e);
                    std::process::exit(1);
                });
    
            if !status.success() {
                eprintln!("Linking failed.");
                std::process::exit(1);
            }
    
            if needs_temp_obj {
                fs::remove_file(&obj_path).expect("Failed to remove temporary object file");
            }
        }
    }
}