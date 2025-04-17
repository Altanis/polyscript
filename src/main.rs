#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![feature(let_chains)]

use std::fs;

mod frontend;
mod utils;

fn main() {
    let program = fs::read_to_string("scripts/main.ps").expect("Invalid source file.");
    let mut lexer = frontend::lexer::Lexer::new(program);
    let tokens = lexer.tokenize();

    if let Err(e) = tokens {
        eprintln!("{}", e);
    } else {
        println!("Compiling finished! {} tokens produced... reading all:", lexer.get_tokens().len());
        for token in lexer.get_tokens().iter() {
            println!("{}", token);
        }
    }
}