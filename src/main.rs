#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![allow(non_upper_case_globals)]
#![allow(clippy::needless_return)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![feature(let_chains)]
#![feature(if_let_guard)]

use std::fs;
use std::path::Path;
use std::rc::Rc;

use frontend::ast::AstNode;
use frontend::token_parser::Parser;
use middle::semantic_analyzer::SemanticAnalyzer;
use utils::kind::Token;

mod frontend;
mod middle;
mod utils;

pub const READ_TOKENS: bool = false;
pub const PARSE_TOKENS: bool = true;
pub const SEMANTIC_ANALYSIS: bool = true;
pub const PRINT: bool = true;

fn generate_tokens(program: String) -> (Vec<String>, Vec<Token>) {
    let mut lexer = frontend::lexer::Lexer::new(program);
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

fn analyze_tokens(lined_source: Vec<String>, program: frontend::ast::AstNode) -> (SemanticAnalyzer, AstNode) {
    let mut analyzer = SemanticAnalyzer::new(Rc::new(lined_source));
    match analyzer.analyze(program) {
        Err(errs) => {
            println!("{} errors emitted... printing:", errs.len());
            for err in errs {
                eprintln!("{}", err);
            }

            std::process::exit(1);
        }
        Ok(program) => (analyzer, program),
    }
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
        // dbg!(&program);
        // println!("{}", program);

        if SEMANTIC_ANALYSIS {
            let (analyzer, program) = analyze_tokens(lined_source, program);
            
            if PRINT {
                println!("--- ANNOTATED AST ---");
                println!("{}", program);

                println!("--- SEMANTIC ANALYZER ---");
                println!("{}", analyzer);
            }
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

        let program = fs::read_to_string(&path).expect("Invalid source file.");
        let (lined_source, tokens) = generate_tokens(program);
        let program_node = parse_tokens(lined_source.clone(), tokens);
        // let (_, program) = analyze_tokens(lined_source, program_node);

        // println!("{}", program);
    }

    println!("All files checked.");
}

fn main() {
    std::env::set_var("RUST_BACKTRACE", "1");

    // assert_scripts_work();
    test_main_script();
}
