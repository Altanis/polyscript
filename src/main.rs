#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![allow(non_upper_case_globals)]
#![allow(clippy::needless_return)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::module_inception)]
#![feature(if_let_guard)]

use crate::compiler::Compiler;

mod frontend;
mod mir;
mod backend;
mod utils;
mod compiler;

fn main() {
    let compiler = Compiler::new("scripts/main.ps");
    compiler.run();
}