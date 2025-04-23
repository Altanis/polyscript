use colored::*;

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

pub const INT_TYPE: &str = "int";
pub const FLOAT_TYPE: &str = "float";
pub const BOOL_TYPE: &str = "bool";
pub const STRING_TYPE: &str = "string";
pub const VOID_TYPE: &str = "void";

pub const LET_KEYWORD: &str = "let";
pub const CONST_KEYWORD: &str = "const";
pub const CLASS_KEYWORD: &str = "class";
pub const OVERRIDE_KEYWORD: &str = "override";
pub const TRUE_KEYWORD: &str = "true";
pub const FALSE_KEYWORD: &str = "false";
pub const FN_KEYWORD: &str = "fn";
pub const FOR_KEYWORD: &str = "for";
pub const WHILE_KEYWORD: &str = "while";
pub const RETURN_KEYWORD: &str = "return";
pub const BREAK_KEYWORD: &str = "break";
pub const CONTINUE_KEYWORD: &str = "continue";
pub const IF_KEYWORD: &str = "if";
pub const ELSE_KEYWORD: &str = "else";
pub const THROW_KEYWORD: &str = "throw";

pub const END_OF_LINE: char = ';';
pub const OPEN_PARENTHESIS: char = '(';
pub const CLOSE_PARENTHESIS: char = ')';
pub const OPEN_BRACKET: char = '[';
pub const CLOSE_BRACKET: char = ']';
pub const OPEN_CURLY_BRACKET: char = '{';
pub const CLOSE_CURLY_BRACKET: char = '}';
pub const COMMA: char = ',';
pub const COLON: char = ':';

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeKind {
    Int,
    Float,
    Bool,
    String,
    Void
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operation {
    // UNARY
    Negate, // !
    BitwiseNegate,
    Increment,
    Decrement,

    // BINARY
    Plus,
    Minus,
    Mul,
    Exp,
    Div,
    Mod,
    PlusEq,
    MinusEq,
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

impl Operation {
    pub fn is_postfix(&self) -> bool {
        matches!(self, Operation::Increment | Operation::Decrement)
    }

    pub fn is_unary(&self) -> bool {
        matches!(
            self,
            Operation::Negate
                | Operation::BitwiseNegate
                | Operation::Increment
                | Operation::Decrement
                | Operation::Plus
                | Operation::Minus
        )
    }

    pub fn is_binary(&self) -> bool {
        matches!(
            self,
            Operation::Plus
                | Operation::Minus
                | Operation::Mul
                | Operation::Exp
                | Operation::Div
                | Operation::Mod
                | Operation::PlusEq
                | Operation::MinusEq
                | Operation::MulEq
                | Operation::DivEq
                | Operation::ModEq
                | Operation::BitwiseAnd
                | Operation::BitwiseOr
                | Operation::BitwiseXor
                | Operation::RightBitShift
                | Operation::LeftBitShift
                | Operation::Assign
        )
    }

    pub fn is_conditional(&self) -> bool {
        matches!(
            self,
            Operation::And
                | Operation::Or
                | Operation::GreaterThan
                | Operation::Geq
                | Operation::LessThan
                | Operation::Leq
                | Operation::Equivalence
        )
    }
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Operation::Negate => SUB_TOKEN.to_string(),
            Operation::BitwiseNegate => BITWISE_NEGATE_TOKEN.to_string(),
            Operation::Increment => format!("{}{}", ADD_TOKEN, ADD_TOKEN),
            Operation::Decrement => format!("{}{}", SUB_TOKEN, SUB_TOKEN),
            Operation::Plus => ADD_TOKEN.to_string(),
            Operation::Minus => SUB_TOKEN.to_string(),
            Operation::Mul => MUL_TOKEN.to_string(),
            Operation::Exp => format!("{}{}", MUL_TOKEN, MUL_TOKEN),
            Operation::Div => DIV_TOKEN.to_string(),
            Operation::Mod => MOD_TOKEN.to_string(),
            Operation::PlusEq => format!("{}{}", ADD_TOKEN, ASSIGNMENT_TOKEN),
            Operation::MinusEq => format!("{}{}", SUB_TOKEN, ASSIGNMENT_TOKEN),
            Operation::MulEq => format!("{}{}", MUL_TOKEN, ASSIGNMENT_TOKEN),
            Operation::DivEq => format!("{}{}", DIV_TOKEN, ASSIGNMENT_TOKEN),
            Operation::ModEq => format!("{}{}", MOD_TOKEN, ASSIGNMENT_TOKEN),
            Operation::BitwiseAnd => BITWISE_AND_TOKEN.to_string(),
            Operation::BitwiseOr => BITWISE_OR_TOKEN.to_string(),
            Operation::BitwiseXor => BITWISE_XOR_TOKEN.to_string(),
            Operation::RightBitShift => format!("{}{}", GREATER_THAN_TOKEN, GREATER_THAN_TOKEN),
            Operation::LeftBitShift => format!("{}{}", LESS_THAN_TOKEN, LESS_THAN_TOKEN),
            Operation::Assign => ASSIGNMENT_TOKEN.to_string(),
            Operation::And => format!("{}{}", BITWISE_AND_TOKEN, BITWISE_AND_TOKEN),
            Operation::Or => format!("{}{}", BITWISE_OR_TOKEN, BITWISE_OR_TOKEN),
            Operation::GreaterThan => GREATER_THAN_TOKEN.to_string(),
            Operation::Geq => format!("{}{}", GREATER_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::LessThan => LESS_THAN_TOKEN.to_string(),
            Operation::Leq => format!("{}{}", LESS_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::Equivalence => format!("{}{}", ASSIGNMENT_TOKEN, ASSIGNMENT_TOKEN),
        };

        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NumberKind {
    // INTEGERS
    Decimal,
    Binary,
    Octal,
    Hex,

    // FLOATS
    Float
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LoopKind {
    For,
    While
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ControlFlowKind {
    Return,
    Break,
    Continue,
    Throw
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    Identifier,
    Operator(Operation),
    Numeric(NumberKind),
    Type(TypeKind),
    VariableDeclaration(bool),
    ClassDeclaration,
    Override,
    Boolean,
    FunctionDeclaration,
    Loop(LoopKind),
    ControlFlow(ControlFlowKind),
    If,
    Else,
    EndOfLine,
    OpenParenthesis,
    CloseParenthesis,
    OpenBracket,
    CloseBracket,
    OpenCurlyBracket,
    CloseCurlyBracket,
    Comma,
    Colon,
    EndOfFile
}

#[derive(Debug, Clone, Copy)]
pub struct Position {
    pub line: usize,
    pub column: usize
}

impl Default for Position {
    fn default() -> Self {
        Position { line: 1, column: 1 }
    }
}

#[derive(Default, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub start_pos: Position,
    pub end_pos: Position
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,
            "{}..{} | {}:{} → {}:{}",
            self.start,
            self.end,
            self.start_pos.line,
            self.start_pos.column,
            self.end_pos.line,
            self.end_pos.column
        )   
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,
            "starting line {}, starting col {} | span {}..{} | ending line {}, ending col {}",
            self.start_pos.line,
            self.start_pos.column,
            self.start,
            self.end,
            self.end_pos.line,
            self.end_pos.column
        )
    }
}

impl Span {
    pub fn set_end_from_values(mut self, index: usize, line: usize, column: usize) -> Span {
        self.end = index;
        self.end_pos = Position { line, column };
        
        self
    }

    pub fn set_end_from_span(mut self, span: Span) -> Span {
        self.end = span.end;
        self.end_pos = span.end_pos;
        
        self
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    /// The true value in source.
    value: String,
    /// The type of token.
    token_kind: TokenKind,
    /// Details about the token's placement in source.
    span: Span
}

impl Token {
    pub fn new(value: String, token_type: TokenKind, span: Span) -> Token {
        Token { value, token_kind: token_type, span }
    }

    pub fn get_value(&self) -> &String {
        &self.value
    }

    pub fn get_token_kind(&self) -> TokenKind {
        self.token_kind
    }

    pub fn get_span(&self) -> Span {
        self.span
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let token_type_str = match &self.token_kind {
            TokenKind::Identifier => "Identifier".cyan(),
            TokenKind::Operator(op) => format!("Operator::{:?}", op).bright_magenta(),
            TokenKind::Numeric(n) => format!("Number::{:?}", n).blue(),
            TokenKind::Type(value_type) => format!("TypeKind::{:?}", value_type).bright_blue(),
            TokenKind::VariableDeclaration(true) => "Let Declaration".bright_green(),
            TokenKind::VariableDeclaration(false) => "Const Declaration".green(),
            TokenKind::ClassDeclaration => "Class Declaration".bright_cyan(),
            TokenKind::Override => "Override".bright_black(),
            TokenKind::Boolean => "Boolean".magenta(),
            TokenKind::FunctionDeclaration => "Function".bright_red(),
            TokenKind::Loop(LoopKind::For) => "Loop::For".bright_white(),
            TokenKind::Loop(LoopKind::While) => "Loop::While".white(),
            TokenKind::ControlFlow(cf) => format!("Control::{:?}", cf).bright_red(),
            TokenKind::If => "If".purple(),
            TokenKind::Else => "Else".purple(),
            TokenKind::EndOfLine => "EndOfLine".dimmed(),
            TokenKind::OpenParenthesis => "OpenParen".dimmed(),
            TokenKind::CloseParenthesis => "CloseParen".dimmed(),
            TokenKind::OpenBracket => "OpenBracket".dimmed(),
            TokenKind::CloseBracket => "CloseBracket".dimmed(),
            TokenKind::OpenCurlyBracket => "OpenCurly".dimmed(),
            TokenKind::CloseCurlyBracket => "CloseCurly".dimmed(),
            TokenKind::Comma => "Comma".dimmed(),
            TokenKind::Colon => "Colon".dimmed(),
            TokenKind::EndOfFile => "END OF FILE".into()
        };

        write!(
            f,
            "{} ({}) at [{}]",
            self.value.bold(),
            token_type_str,
            self.span
        )
    }
}