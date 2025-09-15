# Polyscript

Polyscript is a Rust-like toy language with static typing, reference counting, and an LLVM AOT compiler.

***

## Documentation Structure

> NOTE: The documentation for this language is incomplete.

The language specification is divided into several parts:

1.  [**Syntax and Basics**](./DOCS/01-syntax-and-basics.md): Variables, primitive types, operators, and basic syntax.
2.  [**Control Flow**](./DOCS/02-control-flow.md): `if-else` expressions, `for` and `while` loops.
3.  [**Compound Types**](./DOCS/03-compound-types.md): Defining `struct` and `enum` types.
4.  [**Functions and Closures**](./DOCS/04-functions-and-closures.md): Defining and calling functions, differentiating functions from closures.
5.  [**Generics**](./DOCS/05-generics.md): Writing code that works with multiple types.
6.  [**Implementations and Traits**](./DOCS/06-traits-and-impls.md): Defining behavior on types and describing types via shared behavior.
7.  [**Modules**](./DOCS/07-modules.md): Code organization using `import` and `export`.
7.  [**Standard Library**](./DOCS/08-stdlib.md): Extra features provided by the native standard library.
8.  [**Memory Model**](./DOCS/09-memory-model.md): A deep dive into Polyscript's stack, heap, and reference counting system.
9.  [**Compiler Internals**](./DOCS/10-compiler-internals.md): An explanation of the compiler's architecture and compilation pipeline.

## Usage

After compiling the compiler into an executable `./polyscriptcc`, running `./polyscriptcc --help` will give further instructions as to how to compile a Polyscript program. The native standard library is provided [here](./scripts/stdlib).