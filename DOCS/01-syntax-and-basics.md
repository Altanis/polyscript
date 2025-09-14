## Comments

The Polyscript compiler ignores comments, which borrows the syntax from C-like languages and Rust.

```rs
// This is a single line comment.

/* This is a
    MULTI-LINE
comment*/
```

## Primitives

Polyscript defines multiple primitive, builtin types.

| Types | Description | Examples |
| ----- | ----------- | -------- |
| `int` | A 64-bit signed integer. | `4`, `-3` |
| `float` | A 64-bit floating-point number. | `3.14`, `-0.5` |
| `bool` | A boolean value in a binary of `true` and `false` states. | `true`, `false` |
| `char` | A single, 1-byte Unicode scalar value. | `'c'` |
| `str` | An immutable, statically known string. | `"hi"` |

### Numeric Literals

Numeric literals may be expressed in four ways (binary, `0b01`; octal, `0o0172`; decimal, `13`; hexadecimal, `0xFF`). Floating point literals may be written normally, like `0.123`, or in scientific notation, like `6.022e23`.

### String Literals
String literals are enclosed in double quotes (`"`) and character literals in single quotes (`'`). They support common escape sequences.
| Escape Sequence | Meaning                                                      |
|-----------------|--------------------------------------------------------------|
| `\n`            | Newline                                                      |
| `\r`            | Carriage return                                              |
| `\t`            | Tab                                                          |
| `\\`            | Backslash                                                    |
| `\'`            | Single quote                                                 |
| `\"`            | Double quote                                                 |
| `\0`            | Null character                                               |
| `\xHH`          | 2-digit hex escape (e.g., `\x41` is `A`)                     |
| `\u{...}`       | Unicode escape up to 6 hex digits (e.g., `'\u{1F600}'` is 😀) |

## Operators

Polyscript supports a standard set of arithmetic, bitwise, comparison, and logical operators, with precedence rules similar to C-family languages.

| Precedence | Operator Category       | Operators                                                                                                                                                                                            | Associativity |
| :--------- | :---------------------- | :--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | :------------ |
| 15         | Field Access            | `.`                                                                                                                                                                                                  | Left-to-right |
| 14         | Function Call           | `()`                                                                                                                                                                                                 | Left-to-right |
| 13         | Unary                   | `-` (negation), `!` (logical NOT), `~` (bitwise NOT)                                                                                                                                                 | Right-to-left |
| 12         | Exponentiation          | `**`                                                                                                                                                                                                 | Right-to-left |
| 11         | Multiplicative          | `*`, `/`, `%`                                                                                                                                                                                        | Left-to-right |
| 10         | Additive                | `+`, `-`                                                                                                                                                                                             | Left-to-right |
| 9          | Bitwise Shift           | `<<`, `>>`                                                                                                                                                                                           | Left-to-right |
| 8          | Bitwise AND             | `&`                                                                                                                                                                                                  | Left-to-right |
| 7          | Bitwise XOR             | `^`                                                                                                                                                                                                  | Left-to-right |
| 6          | Bitwise OR              | `|`                                                                                                                                                                                                  | Left-to-right |
| 5          | Comparison              | `==`, `!=`, `<`, `<=`, `>`, `>=`                                                                                                                                                                      | Left-to-right |
| 4          | Logical AND             | `&&`                                                                                                                                                                                                 | Left-to-right |
| 3          | Logical OR              | `||`                                                                                                                                                                                                 | Left-to-right |
| 2          | Assignment              | `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `**=`, `&=`, `|=`, `^=`, `<<=`, `>>=`                                                                                                                                 | Right-to-left |
| 1          | Type Cast               | `as`                                                                                                                                                                                                 | Left-to-right |

## Variables

Polyscript recognizes mutable `let` variable declarations and immutable `const` variable declarations. `let` declarations can optionally be annotated with a type,
while `const` declarations must be annotated with one. `const` declarations may only take on primitive literals for values, while `let` may bind variables to any
expression.

```rs
let x: int = 4; // An integer `x` bound to value 4.
const y: float = 4.0; // An immutable, static variable `y: float` bound to the value `4.0`.
```

> NOTE: Programs do not have entry points, so variables and other nodes that would typically be function-level items may be defined with no enclosing function scope.