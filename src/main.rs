#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![allow(non_upper_case_globals)]
#![allow(clippy::needless_return)]
#![feature(let_chains)]

use std::fs;
use std::path::Path;

mod frontend;
mod utils;

pub const READ_TOKENS: bool = false;
pub const PARSE_TOKENS: bool = true;

fn generate_tokens(program: String) -> (Vec<String>, Vec<utils::kind::Token>) {
    let mut lexer = frontend::lexer::Lexer::new(program);
    let tokens = lexer.tokenize();

    if let Err(e) = tokens {
        eprintln!("{}", e);
        std::process::exit(1);
    }

    (lexer.take_lined_source(), lexer.take_tokens())
}

fn parse_tokens(lined_source: Vec<String>, tokens: Vec<utils::kind::Token>) -> frontend::ast::AstNode {
    let mut parser = frontend::token_parser::Parser::new(lined_source, tokens);

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
        let program = parse_tokens(lined_source, tokens);
        println!("{}", program);
    }
}

fn assert_scripts_work() {
    let mut paths = Vec::new();
    let path = Path::new("scripts/tests");

    if let Ok(entries) = fs::read_dir(path) {
        paths.extend(
            entries.filter_map(Result::ok)
                   .map(|entry| entry.path())
                   .filter(|path| path.is_file())
        );
    }

    for path in paths {
        println!("Asserting {} can be lexed and parsed...", path.display());

        let program = fs::read_to_string(&path).expect("Invalid source file.");
        let (lined_source, tokens) = generate_tokens(program);
        let program_node = parse_tokens(lined_source, tokens);

        println!("{}", program_node);

        println!("Assertion complete!\n");
    }

    println!("All files checked.");
}

fn main() {
    // assert_scripts_work();
    test_main_script();
}