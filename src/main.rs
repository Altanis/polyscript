#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![allow(non_upper_case_globals)]
#![allow(clippy::needless_return)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::module_inception)]
#![feature(if_let_guard)]

use std::fs;
use std::path::Path;
use std::process::Command;
use std::rc::Rc;

use colored::Colorize;
use frontend::syntax::ast::AstNode;
use frontend::syntax::parser::Parser;
use frontend::semantics::analyzer::SemanticAnalyzer;
use inkwell::context::Context;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple};
use inkwell::OptimizationLevel;
use utils::kind::Token;

use crate::backend::codegen::codegen::CodeGen;
use crate::backend::optimizations::escape_analysis;
use crate::frontend::syntax::lexer::Lexer;
use crate::mir::builder::MIRBuilder;
use crate::mir::ir_node::MIRNode;

mod frontend;
mod mir;
mod backend;
mod utils;

pub const READ_TOKENS: bool = false;
pub const PARSE_TOKENS: bool = true;
pub const SEMANTIC_ANALYSIS: bool = true;
pub const PRINT: bool = true;

fn generate_tokens(program: String) -> (Vec<String>, Vec<Token>) {
    let mut lexer = Lexer::new(program);
    let tokens = lexer.tokenize();

    if let Err(e) = tokens {
        eprintln!("{}", e);
        std::process::exit(1);
    }

    lexer.extract()
}

fn parse_tokens(lined_source: Vec<String>, tokens: Vec<Token>) -> AstNode {
    let mut parser = Parser::new(lined_source, tokens);

    match parser.parse() {
        Err(errs) => {
            println!("{} errors emitted... printing:", errs.len());
            for err in errs {
                eprintln!("{}", err);
            }

            std::process::exit(1);
        }
        Ok(program) => program,
    }
}

fn analyze_ast(lined_source: Vec<String>, program: AstNode) -> (AstNode, SemanticAnalyzer) {
    let mut analyzer = SemanticAnalyzer::new(Rc::new(lined_source));
    match analyzer.analyze(program) {
        Err(errs) => {
            println!("{} errors emitted... printing:", errs.len());
            for err in errs {
                eprintln!("{}", err);
            }

            std::process::exit(1);
        }
        Ok(program) => (program, analyzer),
    }
}

fn lower_ast_to_mir<'a>(program: &mut AstNode, analyzer: &'a mut SemanticAnalyzer) -> (MIRBuilder<'a>, MIRNode) {
    let mut builder = MIRBuilder::new(analyzer);
    let program = builder.build(program);

    (builder, program)
}

fn optimize(program: &mut MIRNode, analyzer: &mut SemanticAnalyzer) {
    escape_analysis::init(program, analyzer);
}

fn compile_ast(program: AstNode, analyzer: &SemanticAnalyzer) {
    let context = Context::create();
    let module = context.create_module("a");
    let builder = context.create_builder();

    let mut codegen = CodeGen::new(&context, &builder, &module, analyzer);
    codegen.compile_program(&program);

    let path = Path::new("bin/output.ll");
    module.print_to_file(path).expect("couldn't write to output.ll");

    Target::initialize_all(&InitializationConfig::default());

    let target_triple = TargetTriple::create("arm64-apple-darwin");
    module.set_triple(&target_triple);

    let target = Target::from_triple(&target_triple).expect("Target not found");
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "apple-m2",
            "",
            OptimizationLevel::None,
            RelocMode::Default,
            CodeModel::Default,
        )
        .expect("Failed to create target machine");

    let asm_path = Path::new("bin/output_macos.s");
    target_machine.write_to_file(&module, FileType::Assembly, asm_path).expect("Failed to write assembly");

    Command::new("clang")
        .args(["bin/output_macos.s", "-o", "bin/a"])
        .status()
        .expect("Failed to run clang");
}

fn test_main_script() {
    let program = fs::read_to_string("scripts/main.ps").expect("Invalid source file.");
    let (lined_source, tokens) = generate_tokens(program);

    if READ_TOKENS {
        println!("Reading tokens...");
        for token in tokens.iter() {
            println!("{}", token);
        }
    }

    if PARSE_TOKENS {
        let program = parse_tokens(lined_source.clone(), tokens);

        if SEMANTIC_ANALYSIS {
            let (mut program, mut analyzer) = analyze_ast(lined_source, program);
            
            if PRINT {
                println!("--- AST ---");
                
                let mut format_str = String::new();
                let _ = program.fmt_with_indent(&mut format_str, 0, Some(&analyzer.symbol_table));
                println!("{}", format_str);
            }

            let (ir_builder, mut mir_program) = lower_ast_to_mir(&mut program, &mut analyzer);
            let ir_builder_str = format!("{}", ir_builder);
            std::mem::drop(ir_builder);

            optimize(&mut mir_program, &mut analyzer);

            println!("--- SEMANTIC ANALYZER ---");
            println!("{}", analyzer);

            println!("--- MIR BUILDER ---");
            println!("{}", ir_builder_str);

            println!("--- MIR PROGRAM ---");
            let mut format_str = String::new();
            let _ = mir_program.fmt_with_indent(&mut format_str, 0, Some(&analyzer.symbol_table));
            println!("{}", format_str);

            compile_ast(program, &analyzer);
        }
    }
}

fn assert_scripts_work() {
    let mut paths = vec![];
    let path = Path::new("scripts/tests");

    if let Ok(entries) = fs::read_dir(path) {
        paths.extend(
            entries
                .filter_map(Result::ok)
                .map(|entry| entry.path())
                .filter(|path| path.is_file()),
        );
    }

    for path in paths {
        println!("Asserting {} compiles well...", path.display());

        let code = fs::read_to_string(&path).expect("Invalid source file.");
        let (lined_source, tokens) = generate_tokens(code.to_string());
        let program = parse_tokens(lined_source.clone(), tokens);
        let (mut program, mut analyzer) = analyze_ast(lined_source, program);
        let (_, mut mir_program) = lower_ast_to_mir(&mut program, &mut analyzer);
        optimize(&mut mir_program, &mut analyzer);

        // println!("{}", program);
    }

    println!("All files checked.");
}

fn test_escape_analysis() {
    let code = r#"fn test1() {
            let outer_ref = {
                let f = 60;
                &f
            };

            const val = *outer_ref;
        }

        struct Point { x: int; }
        fn test2() {
            let p2 = Point { x: 2 };
            let x = p2.x;
        }

        fn create_point(): Point {
            let p3 = Point { x: 1 };
            return p3;
        }

        fn create_ref_point(): &Point {
            let p4 = Point { x: 1 };
            &p4
        }


        struct Inner { public val: int; }
        struct Outer { public data: Inner; }
        fn test5() {
            let outer_instance = heap Outer { data: Inner { val: 0 } };
            let local_inner = Inner { val: 100 };
            outer_instance.data = local_inner;
        }

        struct Config { public setting: bool; }
        fn helper_test6(c: &Config) {}
        fn test6() {
            let my_config = Config { setting: true };
            helper_test6(&my_config);
        }

        struct Message { public content: string; }
        fn test7(): Message {
            if (true) {
                let m = Message { content: "hello" };
                return m;
            };
            
            return Message { content: "world" };
        }

        struct A { public b: B; }
        struct B { public c: C; }
        struct C { public val: int; }
        fn test8(): C {
            let my_a = A { b: B { c: C { val: 1 } } };
            let my_b = my_a.b;
            let my_c = my_b.c;
            return my_c;
        }
        
        fn id<T>(x: T): T {
            return x;
        }
        
        fn test9(): &int {
            let ester = 10;
            return id(&ester);
        }
        "#;

    let (lined_source, tokens) = generate_tokens(code.to_string());
    let program = parse_tokens(lined_source.clone(), tokens);
    let (mut program, mut analyzer) = analyze_ast(lined_source, program);
    let (_, mut mir_program) = lower_ast_to_mir(&mut program, &mut analyzer);
    optimize(&mut mir_program, &mut analyzer);

    let expected = [
        ("f",              crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("outer_ref",      crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("p2",             crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("x",              crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("p3",             crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("p4",             crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("outer_instance", crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("local_inner",    crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("my_config",      crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("m",              crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("my_a",           crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("my_b",           crate::frontend::semantics::analyzer::AllocationKind::Stack),
        ("my_c",           crate::frontend::semantics::analyzer::AllocationKind::Heap),
        ("ester",          crate::frontend::semantics::analyzer::AllocationKind::Heap)
    ];

    println!("{}", analyzer.symbol_table);

    for (name, alloc_type) in expected {
        for (&id, _) in analyzer.symbol_table.scopes.iter() {
            if let Some(symbol) = analyzer.symbol_table.find_value_symbol_in_scope(name, id) {
                if symbol.allocation_kind == alloc_type {
                    println!("{}", format!("{name} allocates properly [expected {:?} and found {:?}]!", alloc_type, symbol.allocation_kind).green());
                } else {
                    println!("{}", format!("{name} does not allocate properly [expected {:?} but found {:?}]...", alloc_type, symbol.allocation_kind).red());
                }

                break;
            }
        }

    }
}

fn main() {
    unsafe {
        std::env::set_var("RUST_BACKTRACE", "1");
    }

    // assert_scripts_work();
    test_main_script();
    // test_escape_analysis();
}