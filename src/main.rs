#![allow(dead_code)]
#![allow(clippy::wrong_self_convention)]
#![allow(non_upper_case_globals)]
#![allow(clippy::needless_return)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::module_inception)]
#![allow(clippy::upper_case_acronyms)]

use clap::{Parser, ValueEnum};
use inkwell::OptimizationLevel;
use std::{fs, path::{Path, PathBuf}};

use crate::compiler::{Compiler, CompilerConfig, EmitTarget, EmitType};

mod backend;
mod compiler;
mod frontend;
mod mir;
mod utils;

#[derive(Parser, Debug)]
#[command(author = "Altanis", version = "1.0.0", about = "A Rust-like toy language with reference counting and an LLVM AOT compiler.", long_about = None)]
struct CliArgs {
    /// The entry source file for compilation
    #[arg(required = true)]
    entry_file: String,

    /// Set the optimization level
    #[arg(short = 'O', value_enum, default_value_t = OptLevelArg::O0, verbatim_doc_comment, ignore_case(true))]
    opt_level: OptLevelArg,

    /// Generate debug symbols
    #[arg(short, long)]
    debug_symbols: bool,

    /// Emit assembly code
    #[arg(short = 'S', long, value_name = "FILE")]
    emit_asm: Option<PathBuf>,

    /// Emit LLVM IR
    #[arg(long, value_name = "FILE")]
    emit_llir: Option<PathBuf>,

    /// Compile and assemble, but do not link
    #[arg(short = 'c', value_name = "FILE")]
    emit_obj: Option<PathBuf>,

    /// Specify the output file name for the final executable
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,

    /// The target triple to compile for
    #[arg(long, value_name = "TRIPLE")]
    target: Option<String>,

    /// The target CPU to compile for
    #[arg(long, value_name = "CPU")]
    cpu: Option<String>,

    /// CPU features to enable or disable
    #[arg(long, value_name = "FEATURES")]
    features: Option<String>,

    /// The linker to use for the final executable
    #[arg(long, value_name = "LINKER")]
    linker: Option<String>,

    /// The standard library to compile with.
    #[arg(long, value_name = "STDLIB")]
    stdlib: Option<String>
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum OptLevelArg {
    /// -O0: No optimizations
    #[value(alias = "0")]
    O0,
    /// -O1: Basic optimizations
    #[value(alias = "1")]
    O1,
    /// -O2: More optimizations
    #[value(alias = "2")]
    O2,
    /// -O3: Aggressive optimizations
    #[value(alias = "3")]
    O3,
    /// -Os: Optimize for size
    #[value(alias = "s")]
    Os,
    /// -Oz: Aggressively optimize for size
    #[value(alias = "z")]
    Oz,
}

fn main() {
    let cli = CliArgs::parse();

    let mut emit_targets: Vec<_> = [(cli.emit_asm, EmitType::Asm), (cli.emit_obj, EmitType::Obj), (cli.emit_llir, EmitType::LLIR), (cli.output, EmitType::Executable)]
        .into_iter()
        .filter_map(|(opt, kind)| opt.map(|path| EmitTarget { kind, path }))
        .collect();

    if emit_targets.is_empty() {
        let stem = Path::new(&cli.entry_file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("a.out");
        emit_targets.push(EmitTarget {
            kind: EmitType::Executable,
            path: PathBuf::from(stem),
        });
    };

    let opt_level = match cli.opt_level {
        OptLevelArg::O0 => OptimizationLevel::None,
        OptLevelArg::O1 => OptimizationLevel::Less,
        OptLevelArg::O2 => OptimizationLevel::Default,
        OptLevelArg::O3 => OptimizationLevel::Aggressive,
        OptLevelArg::Os | OptLevelArg::Oz => OptimizationLevel::Default, // Inkwell doesn't have a direct mapping for Os/Oz, map to Default
    };

    if cli.opt_level == OptLevelArg::Os || cli.opt_level == OptLevelArg::Oz {
        println!("[WARN] Optimization levels -Os and -Oz are mapped to -O2 for LLVM.");
    }

    let config = CompilerConfig {
        entry_file: cli.entry_file,
        opt_level,
        target_triple: cli.target.unwrap_or_default(),
        cpu: cli.cpu.unwrap_or_default(),
        emit_targets,
        debug_symbols: cli.debug_symbols,
        features: cli.features.unwrap_or_default(),
        linker: cli.linker.unwrap_or_default(),
        stdlib_path: cli.stdlib.map(|p| fs::canonicalize(p).expect("Standard library path not found or is invalid.")),
    };

    let mut compiler = Compiler::new(config);
    compiler.run();
}