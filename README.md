## todo
- [x] variable declaration
- [x] function declaration
- [x] blocks
- [x] loops
- [x] control flow
- [x] structs
- [x] impl/associated functions/variables
- [x] associated field/function access
- [x] enums
- [x] traits
- [x] generics
- [x] custom types
- [x] references
- [x] function types
- [ ] refactor parser/ast for consistency
- [ ] refactor lexer/token for consistency
- [ ] fix all error formats

NOTE: stdlib should contain:
- io functions (print, err, etc)
- math functions
- traits for common operations (operator overloading maybe)

NOTE: Trailing commas are NOT allowed.

NOTE: Builtin types will eventually be eliminated and implemented by stdlib in this way:
    # traits.ps
        ```
        trait TAddable {
            fn add(this, other: Self): Self;
        }
        ```
    # int.ps
        ```
        type int = __BUILTIN_INTEGER__;
        impl TAddable for int { ... }
        ```