# 02: Control Flow

## Blocks
A block is a sequence of statements enclosed in curly braces `{}`. Blocks create a new lexical scope. Variables declared inside a block are not visible outside of it. A block itself is an expression, evaluating to the value of its last expression. If the last statement in a block ends with a semicolon, the block evaluates to `void`.

```rs
let x: int = {
    let y = 7;
    let z = 3;
    y * z + 1 // The block resolves to this value, `22`.
};

// y and z are not accessible outside of the block bound to `x`.

// This block resolves to no value, as the last statement takes on the type `void`.
{
    let y = 3;
}
```

## If/Else Statements

Polyscript recognizes if/else blocks as selection statements that are conditionally executed. Akin to Rust, if/else statements resolve to the type of the block they have.
```rs
if (x == 4) {
    // This block only runs if x == 4.
} else if (x == 5) {
    // This block only runs if x == 5.
} else {
    // This block only runs if x != 4, x != 5.
}; // All if statements must be terminated with semicolons as a consequence of them being expressions.

let boolean_value = true;
// `integer_value` holds an integer literal that may either take on the value `0` or `1`, depending on the condition.
// This is analagous to the ternay operator in C-like languages.
let integer_value = if (boolean_value) { 1 } else { 0 };

if (x == 5) {
    3
} else if (x == 6) {
    // "hi" <-- ERROR. The types each branch in an if statement can resolve to must be equivalent.
    4
} else {
    // Although this function is of type `never`, it's allowed, since this value will never be reached
    // and so the user does not have to worry about divergent types stemming from an if statement.
    function_that_exits_process()
}
```

## While Loops & For Loops

Polyscript defines `for` and `while` loops analagous to C-like languages.

```rs
let i = 0;
while (i < 5) { // This loop runs as long as the condition is true, i.e. as long as i < 5.
    i += 1;
}

// For loops follow the familiar for (initializer; condition; increment) syntax.
for (let j = 0; j < 5; j += 1) {
    if (i == 0) continue; // This continues with the next iteration of a for/while loop.
    if (i == 3) break; // This stops the loop at this point.
    // A return statement, if used validly, will also stop the execution of a loop.
}

// And this is a loop that never ends.
for (;;) {}
```