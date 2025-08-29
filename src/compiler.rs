use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::rc::Rc;

use inkwell::context::Context;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple};
use inkwell::OptimizationLevel;

use crate::backend::codegen::codegen::CodeGen;
use crate::backend::optimizations::{capture_analysis, escape_analysis};
use crate::frontend::semantics::analyzer::SemanticAnalyzer;
use crate::frontend::syntax::ast::AstNode;
use crate::frontend::syntax::lexer::Lexer;
use crate::frontend::syntax::parser::Parser;
use crate::mir::builder::MIRBuilder;
use crate::mir::ir_node::MIRNode;
use crate::utils::kind::Token;

pub const DEBUG: bool = true;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EmitType {
    Asm,
    Obj,
    LLVMIR,
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
    pub features: String
}

pub struct Compiler {
    config: CompilerConfig,
}

impl Compiler {
    pub fn new(config: CompilerConfig) -> Compiler {
        Compiler { config }
    }

    pub fn run(&self) {
        let program = fs::read_to_string(&self.config.entry_file).expect("Invalid source file.");

        let (lined_source, tokens) = self.generate_tokens(program);
        let program = self.parse_tokens(lined_source.clone(), tokens.clone());
        let (mut program, mut analyzer) = self.analyze_ast(lined_source, program);

        let (ir_builder, mut mir_program) = self.lower_ast_to_mir(&mut program, &mut analyzer);
        let ir_builder_fmt = if DEBUG { format!("{}", ir_builder) } else { String::new() };
        std::mem::drop(ir_builder);

        self.optimize(&mut mir_program, &mut analyzer);
        
        let mut mir_program_fmt = String::new();
        if DEBUG {
            let _ = mir_program.fmt_with_indent(&mut mir_program_fmt, 0, Some(&analyzer.symbol_table));
        }

        self.compile_mir(mir_program, &analyzer);

        if DEBUG {
            println!("--- TOKENS ---");
            for token in tokens.iter() {
                println!("{}", token);
            }

            println!("--- AST ---");
            let mut format_str = String::new();
            let _ = program.fmt_with_indent(&mut format_str, 0, Some(&analyzer.symbol_table));
            println!("{}", format_str);

            println!("--- SEMANTIC ANALYZER ---");
            println!("{}", analyzer);

            println!("--- MIR BUILDER ---");
            println!("{}", ir_builder_fmt);

            println!("--- MIR PROGRAM ---");
            println!("{}", mir_program_fmt);
        }
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

    fn analyze_ast(&self, lined_source: Vec<String>, program: AstNode) -> (AstNode, SemanticAnalyzer) {
        let mut analyzer = SemanticAnalyzer::new(Rc::new(lined_source));
        match analyzer.analyze(program) {
            Err(errs) => {
                println!("{} errors emitted... printing:", errs.len());
                for err in errs {
                    eprintln!("{}", err);
                }

                std::process::exit(1);
            },
            Ok(program) => (program, analyzer)
        }
    }

    fn lower_ast_to_mir<'s>(&self, program: &mut AstNode, analyzer: &'s mut SemanticAnalyzer) -> (MIRBuilder<'s>, MIRNode) {
        let mut builder = MIRBuilder::new(analyzer);
        let program = builder.build(program);

        (builder, program)
    }

    fn optimize(&self, program: &mut MIRNode, analyzer: &mut SemanticAnalyzer) {
        let mut errs = vec![];
        errs.extend(escape_analysis::init(program, analyzer));
        capture_analysis::init(program, analyzer);

        if !errs.is_empty() {
            println!("{} errors emitted... printing:", errs.len());
            for err in errs {
                eprintln!("{}", err);
            }

            std::process::exit(1);
        }
    }

    fn compile_mir(&self, program: MIRNode, analyzer: &SemanticAnalyzer) {
        let context = Context::create();
        let module = context.create_module("main_module");
        let builder = context.create_builder();

        Target::initialize_all(&InitializationConfig::default());

        let target_triple = TargetTriple::create(&self.config.target_triple);
        module.set_triple(&target_triple);

        let target = Target::from_triple(&target_triple).expect("Target not found");
        let target_machine = target.create_target_machine(
            &target_triple,
            &self.config.cpu,
            &self.config.features,
            self.config.opt_level,
            RelocMode::Default,
            CodeModel::Default,
        ).expect("Failed to create target machine");

        module.set_data_layout(&target_machine.get_target_data().get_data_layout());

        if self.config.debug_symbols {
            println!("[WARN] Debug symbols are not supported yet.");
        }

        let mut codegen = CodeGen::new(&context, &builder, &module, analyzer);
        codegen.compile_program(&program);

        if let Some(parent) = self.config.output_file.parent() && !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).expect("Failed to create output directory");
        }
        
        match self.config.emit_type {
            EmitType::LLVMIR => {
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

                let status = Command::new("clang")
                    .arg(&temp_obj_path)
                    .arg("-o")
                    .arg(&self.config.output_file)
                    .status()
                    .expect("Failed to run clang to link the executable");

                if !status.success() {
                    eprintln!("Linking failed.");
                    std::process::exit(1);
                }

                fs::remove_file(&temp_obj_path).expect("Failed to remove temporary object file");
            }
        }
    }
}