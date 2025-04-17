# PolyScript

Toy language that can both be interpreted and compiled to machine code. It can be embedded into games with variables being read at runtime by any language.

## planning board thing
Whitespaces: Ignored
Comments: Started by '#', lasts until end of line
Operations:
    Negate // !,
    BitwiseNegate // ~,
    Increment // ++,
    Decrement // --,

    Add // +,
    Sub // -,
    Mul // *,
    Exp // **,
    Div // /,
    Mod // %,
    AddEq // +=,
    SubEq // -=,
    MulEq // *=,
    DivEq // /=,
    ModEq // %=,
    BitwiseAnd // &,
    BitwiseOr // |,
    BitwiseXor // ^,
    RightBitShift // >>,
    LeftBitShift // <<,
    Assign // =,

    And // &&,
    Or // ||,
    GreaterThan // >,
    Geq, // ≥
    LessThan // <,
    Leq, // ≤
    Equivalence // ==

Numbers:
    42 -> decimal
    0b1010/0B1010 -> binary
    0o7373/0O7373 -> octal
    0xFF/0XFF -> hex
    3.14 -> float
    314e-2/314E-2 -> float

Identifiers:
    int/float/bool/string -> variable types
    int/float/bool/string/void -> return types from function
    let -> mutable var decl
    const -> immutable var decl
    class -> class decl
    override -> polymorphism invocation
    true/false -> boolean literals
    fn -> function decl
    for -> for loop init
    while -> while loop init
    return/break/continue/throw -> control flow keywords
    if/else -> if/else condition init

Symbols:
    ; -> ends line
    () -> starts/ends expression
        ex: (2 + 3 * 4) * 5
    {} -> starts/ends scope
        if (x + 2 == 3) { ... }
    [] -> unused so far
    , -> separator of lists
        function(1, 2, 3)
    : -> invokes type/class inheritance
        let x: int = 5;
        class Dog : Animal { ... }


### notes
most complicated features would be functions/closures, classes/inheritance, imports/exports, async, and a stdlib that supports i/o function (printing, reading files, sockets, event loop, etc.)

builtin functions:
-> io.ps
    -> #print()
    -> #error()
    -> #write_file()
    -> #read_file()
-> sys.ps

    -> #exit()