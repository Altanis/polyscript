pub const NEGATE_TOKEN: char = '!';
pub const BITWISE_NEGATE_TOKEN: char = '~';
pub const ADD_TOKEN: char = '+';
pub const SUB_TOKEN: char = '-';
pub const MUL_TOKEN: char = '*';
pub const DIV_TOKEN: char = '/';
pub const MOD_TOKEN: char = '%';
pub const BITWISE_AND_TOKEN: char = '&';
pub const BITWISE_OR_TOKEN: char = '|';
pub const BITWISE_XOR_TOKEN: char = '^';
pub const ASSIGNMENT_TOKEN: char = '=';
pub const GREATER_THAN_TOKEN: char = '>';
pub const LESS_THAN_TOKEN: char = '<';

pub const COMMENT_TOKEN: char = '#';

#[derive(Debug)]
pub enum Operation {
    // UNARY
    Negate,
    BitwiseNegate,
    Increment,
    Decrement,

    // BINARY
    Add,
    Sub,
    Mul,
    Exp,
    Div,
    Mod,
    AddEq,
    SubEq,
    MulEq,
    DivEq,
    ModEq,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    RightBitShift,
    LeftBitShift,
    Assign,

    // CONDITIONAL
    And,
    Or,
    GreaterThan,
    Geq, // ≥
    LessThan,
    Leq, // ≤
    Equivalence
}

#[derive(Debug)]
pub enum NumberType {
    // INTEGERS
    Decimal,
    Binary,
    Octal,
    Hex,

    // FLOATS
    Float
}

#[derive(Debug)]
pub enum TokenType {
    Identifier,
    Unary(Operation),
    Binary(Operation),
    Conditional(Operation),
    Numeric(NumberType)
}

#[derive(Debug)]
pub struct Token {
    /// The true value in source.
    value: String,
    /// The type of token.
    token_type: TokenType
}

impl Token {
    pub fn new(value: String, token_type: TokenType) -> Token {
        Token { value, token_type }
    }
}