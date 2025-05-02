#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![feature(let_chains)]

use std::fs;

mod frontend;
mod utils;

pub const READ_TOKENS: bool = false;
pub const PARSE_TOKENS: bool = true;

fn main() {
    let program = fs::read_to_string("scripts/main.ps").expect("Invalid source file.");
    let mut lexer = frontend::lexer::Lexer::new(program);
    let tokens = lexer.tokenize();

    if let Err(e) = tokens {
        eprintln!("{}", e);
        std::process::exit(1);
    }

    println!("Lexing finished! {} tokens produced.", lexer.get_tokens().len());

    if READ_TOKENS {
        println!("Reading tokens...");
        for token in lexer.get_tokens().iter() {
            println!("{}", token);
        }
    }

    if PARSE_TOKENS {
        let mut parser = frontend::parser::Parser::new(lexer.take_tokens());
        
        match parser.parse() {
            Ok(program) => {
                println!("Parsing finished!");
                // println!("{}", program);
                dbg!(program);
            },
            Err(errs) => {
                println!("{} errors emitted... printing:", errs.len());
                for err in errs {
                    eprintln!("{}", err);
                }
            }
        }
    }
}