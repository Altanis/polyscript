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
- [x] refactor parser/ast for consistency
- [x] refactor lexer/token for consistency
- [x] fix all error formats
- [x] add mutable parameters

constraints on generics
default impl for ops

NOTE: stdlib should contain:
- io functions (print, err, etc)
- math functions
- traits for common operations (operator overloading maybe)

NOTE: Trailing commas are NOT allowed.
NOTE: ```rs
let x: int; # this declaration is sound
# func(x); # this is an ERROR. x is not defined yet, only forward declared.
if (true) {
    x = 5;
} else {
    x = 4;
}

func(x); # x is now verifiably defined
```