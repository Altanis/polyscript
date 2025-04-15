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

Words: