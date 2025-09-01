use colored::*;
use std::rc::Rc;

use crate::frontend::semantics::analyzer::PrimitiveKind;

pub const NOT_TOKEN: char = '!';
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
pub const FIELD_ACCESS_TOKEN: char = '.';

pub const INT_TYPE: &str = "int";
pub const FLOAT_TYPE: &str = "float";
pub const BOOL_TYPE: &str = "bool";
pub const STATIC_STRING_TYPE: &str = "str";
pub const CHAR_TYPE: &str = "char";
pub const VOID_TYPE: &str = "void"; // NOTE: Programs may not use this type.
pub const NEVER_TYPE: &str = "never";

pub const LET_KEYWORD: &str = "let";
pub const CONST_KEYWORD: &str = "const";
pub const ENUM_KEYWORD: &str = "enum";
pub const STRUCT_KEYWORD: &str = "struct";
pub const IMPL_KEYWORD: &str = "impl";
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
pub const SELF_KEYWORD: &str = "self";
pub const PUBLIC_KEYWORD: &str = "public";
pub const PRIVATE_KEYWORD: &str = "private";
pub const TRAIT_KEYWORD: &str = "trait";
pub const TYPE_KEYWORD: &str = "type";
pub const MUT_KEYWORD: &str = "mut";
pub const AS_KEYWORD: &str = "as";
pub const HEAP_KEYWORD: &str = "heap";
pub const IMPORT_KEYWORD: &str = "import";
pub const FROM_KEYWORD: &str = "from";
pub const EXPORT_KEYWORD: &str = "export";
pub const SIZEOF_KEYWORD: &str = "sizeof";

pub const END_OF_LINE: char = ';';
pub const OPEN_PARENTHESIS: char = '(';
pub const CLOSE_PARENTHESIS: char = ')';
pub const OPEN_BRACKET: char = '[';
pub const CLOSE_BRACKET: char = ']';
pub const OPEN_BRACE: char = '{';
pub const CLOSE_BRACE: char = '}';
pub const COMMA: char = ',';
pub const COLON: char = ':';

pub const STRING_DELIMITER: char = '"';
pub const CHAR_DELIMITER: char = '\'';

#[derive(Debug, Hash, Eq, Clone, Copy, PartialEq, strum_macros::EnumIter)]
pub enum Operation {
    // UNARY
    Not, // !
    Neg, // Negate, i.e. `-1`
    BitwiseNegate,

    // BINARY
    Plus,
    Minus,
    Mul,
    Exp,
    Div,
    Mod,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    RightBitShift,
    LeftBitShift,
    Assign,
    PlusEq,
    MinusEq,
    MulEq,
    ExpEq,
    DivEq,
    ModEq,
    BitwiseAndEq,
    BitwiseOrEq,
    BitwiseXorEq,
    RightBitShiftEq,
    LeftBitShiftEq,

    // CONDITIONAL
    And,
    Or,
    GreaterThan,
    Geq, // ≥
    LessThan,
    Leq,         // ≤
    Equivalence, // ==
    NotEqual,    // !=

    // CALL
    FieldAccess,
    FunctionCall,

    // POINTER OPS
    Dereference,
    ImmutableAddressOf,
    MutableAddressOf,

    // CAST
    As
}

impl Operation {
    pub fn is_unary(self) -> bool {
        matches!(
            self,
            Operation::Not
                | Operation::Neg
                | Operation::BitwiseNegate
                | Operation::Plus
                | Operation::Minus
                | Operation::Mul
                | Operation::BitwiseAnd
                | Operation::Dereference
                | Operation::ImmutableAddressOf
                | Operation::MutableAddressOf
        )
    }

    pub fn is_binary(self) -> bool {
        matches!(
            self,
            Operation::Plus
                | Operation::Minus
                | Operation::Mul
                | Operation::Exp
                | Operation::Div
                | Operation::Mod
                | Operation::BitwiseAnd
                | Operation::BitwiseOr
                | Operation::BitwiseXor
                | Operation::RightBitShift
                | Operation::LeftBitShift
                | Operation::Assign
                | Operation::PlusEq
                | Operation::MinusEq
                | Operation::MulEq
                | Operation::ExpEq
                | Operation::DivEq
                | Operation::ModEq
                | Operation::BitwiseAndEq
                | Operation::BitwiseOrEq
                | Operation::BitwiseXorEq
                | Operation::RightBitShiftEq
                | Operation::LeftBitShiftEq
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
                | Operation::NotEqual
        )
    }

    pub fn is_assignment(&self) -> bool {
        matches!(
            self,
            Operation::Assign
                | Operation::PlusEq
                | Operation::MinusEq
                | Operation::MulEq
                | Operation::ExpEq
                | Operation::DivEq
                | Operation::ModEq
                | Operation::BitwiseAndEq
                | Operation::BitwiseOrEq
                | Operation::BitwiseXorEq
                | Operation::RightBitShiftEq
                | Operation::LeftBitShiftEq
        )
    }

    pub fn binding_power(&self) -> (u8, u8) {
        match self {
            Operation::Assign
            | Operation::PlusEq
            | Operation::MinusEq
            | Operation::MulEq
            | Operation::ExpEq
            | Operation::DivEq
            | Operation::ModEq
            | Operation::BitwiseAndEq
            | Operation::BitwiseOrEq
            | Operation::BitwiseXorEq
            | Operation::RightBitShiftEq
            | Operation::LeftBitShiftEq
            | Operation::NotEqual => (1, 2),

            Operation::Or => (2, 3),

            Operation::And => (3, 4),

            Operation::Equivalence => (4, 5),

            Operation::GreaterThan | Operation::Geq | Operation::LessThan | Operation::Leq => (5, 6),

            Operation::BitwiseOr => (6, 7),

            Operation::BitwiseXor => (7, 8),

            Operation::BitwiseAnd => (8, 9),

            Operation::Plus | Operation::Minus => (9, 10),

            Operation::Mul | Operation::Div | Operation::Mod => (10, 11),

            Operation::LeftBitShift | Operation::RightBitShift => (11, 12),

            Operation::Exp => (12, 11),

            Operation::As => (13, 14),
            Operation::Not | Operation::Neg | Operation::BitwiseNegate => (13, 14),

            Operation::FunctionCall => (14, 0),
            Operation::FieldAccess => (14, 15),

            Operation::Dereference | Operation::ImmutableAddressOf | Operation::MutableAddressOf => (15, 16),
        }
    }

    /// Returns the trait name and if it is a binary operation
    pub fn to_trait_data(&self) -> Option<(String, bool)> {
        match self {
            Operation::Not => Some(("Not".to_string(), false)),
            Operation::Neg => Some(("Neg".to_string(), false)),
            Operation::BitwiseNegate => Some(("BitwiseNegate".to_string(), false)),
            Operation::Plus => Some(("Add".to_string(), true)),
            Operation::Minus => Some(("Subtract".to_string(), true)),
            Operation::Mul => Some(("Multiply".to_string(), true)),
            Operation::Exp => Some(("Exponentiate".to_string(), true)),
            Operation::Div => Some(("Divide".to_string(), true)),
            Operation::Mod => Some(("Modulo".to_string(), true)),
            Operation::BitwiseAnd => Some(("BitwiseAnd".to_string(), true)),
            Operation::BitwiseOr => Some(("BitwiseOr".to_string(), true)),
            Operation::BitwiseXor => Some(("BitwiseXor".to_string(), true)),
            Operation::RightBitShift => Some(("RightBitShift".to_string(), true)),
            Operation::LeftBitShift => Some(("LeftBitShift".to_string(), true)),
            Operation::PlusEq => Some(("AddAssign".to_string(), true)),
            Operation::MinusEq => Some(("SubtractAssign".to_string(), true)),
            Operation::MulEq => Some(("MultiplyAssign".to_string(), true)),
            Operation::ExpEq => Some(("ExponentiateAssign".to_string(), true)),
            Operation::DivEq => Some(("DivideAssign".to_string(), true)),
            Operation::ModEq => Some(("ModuloAssign".to_string(), true)),
            Operation::BitwiseAndEq => Some(("BitwiseAndAssign".to_string(), true)),
            Operation::BitwiseOrEq => Some(("BitwiseOrAssign".to_string(), true)),
            Operation::BitwiseXorEq => Some(("BitwiseXorAssign".to_string(), true)),
            Operation::RightBitShiftEq => Some(("RightBitShiftAssign".to_string(), true)),
            Operation::LeftBitShiftEq => Some(("LeftBitShiftAssign".to_string(), true)),
            Operation::NotEqual => Some(("NotEqual".to_string(), true)),
            Operation::And => Some(("And".to_string(), true)),
            Operation::Or => Some(("Or".to_string(), true)),
            Operation::GreaterThan => Some(("GreaterThan".to_string(), true)),
            Operation::Geq => Some(("GreaterThanOrEqual".to_string(), true)),
            Operation::LessThan => Some(("LessThan".to_string(), true)),
            Operation::Leq => Some(("LessThanOrEqual".to_string(), true)),
            Operation::Equivalence => Some(("Equivalence".to_string(), true)),
            Operation::FieldAccess => None,
            Operation::FunctionCall => None,
            Operation::Dereference => None,
            Operation::ImmutableAddressOf => None,
            Operation::MutableAddressOf => None,
            Operation::Assign => None,
            Operation::As => None
        }
    }

    /// Gives the output type for a default Operation implementation of a trait on a primitive type.
    pub fn to_default_trait_return_type(&self, primitive: PrimitiveKind) -> Option<PrimitiveKind> {
        use Operation::*;
        use PrimitiveKind::*;

        match primitive {
            Int => match self {
                Not => Some(Bool),
                Neg | BitwiseNegate => Some(Int),

                Plus | Minus | Mul | Div | Mod | Exp | BitwiseAnd | BitwiseOr | BitwiseXor
                | RightBitShift | LeftBitShift => Some(Int),

                And | Or | GreaterThan | Geq | LessThan | Leq | Equivalence | NotEqual => Some(Bool),

                PlusEq | MinusEq | MulEq | DivEq | ModEq | ExpEq | BitwiseAndEq | BitwiseOrEq
                | BitwiseXorEq | RightBitShiftEq | LeftBitShiftEq => Some(Void),

                Assign | FieldAccess | FunctionCall | Dereference | ImmutableAddressOf 
                | MutableAddressOf | As => None,
            },

            Float => match self {
                Not => Some(Bool),
                Neg => Some(Float),
                BitwiseNegate => None,

                Plus | Minus | Mul | Div | Mod | Exp => Some(Float),

                BitwiseAnd | BitwiseOr | BitwiseXor | RightBitShift | LeftBitShift => None,

                And | Or | GreaterThan | Geq | LessThan | Leq | Equivalence | NotEqual => Some(Bool),

                PlusEq | MinusEq | MulEq | DivEq | ModEq | ExpEq => Some(Void),

                Assign | BitwiseAndEq | BitwiseOrEq | BitwiseXorEq | RightBitShiftEq 
                | LeftBitShiftEq | FieldAccess | FunctionCall | Dereference 
                | ImmutableAddressOf | MutableAddressOf | As => None,
            },

            Bool => match self {
                Not => Some(Bool),
                And | Or | Equivalence | NotEqual => Some(Bool),

                Neg | Assign | BitwiseNegate | Plus | Minus | Mul | Div | Mod | Exp | PlusEq | MinusEq | MulEq
                | DivEq | ModEq | ExpEq | BitwiseAnd | BitwiseOr | BitwiseXor | BitwiseAndEq | BitwiseOrEq
                | BitwiseXorEq | GreaterThan | Geq | LessThan | Leq | RightBitShift | LeftBitShift
                | RightBitShiftEq | LeftBitShiftEq | FieldAccess | FunctionCall | Dereference
                | ImmutableAddressOf | MutableAddressOf | As => None,
            },

            StaticString => match self {
                Equivalence | NotEqual | GreaterThan | Geq | LessThan | Leq => Some(Bool),

                Neg | Not | BitwiseNegate | Minus | Mul | Div | Mod | Exp | MinusEq | MulEq | DivEq
                | ModEq | ExpEq | BitwiseAnd | BitwiseOr | BitwiseXor | BitwiseAndEq | BitwiseOrEq
                | BitwiseXorEq | RightBitShift | LeftBitShift | RightBitShiftEq | LeftBitShiftEq | And
                | Or | Assign | FieldAccess | FunctionCall | Dereference | ImmutableAddressOf
                | MutableAddressOf | As | Plus | PlusEq => None,
            },

            Char => match self {
                Equivalence | NotEqual | GreaterThan | Geq | LessThan | Leq => Some(Bool),

                Neg | Plus | Minus | Mul | Div | Mod | Exp | PlusEq | MinusEq | MulEq | DivEq | ModEq | ExpEq
                | BitwiseAnd | BitwiseOr | BitwiseXor | BitwiseAndEq | BitwiseOrEq | BitwiseXorEq
                | RightBitShift | LeftBitShift | RightBitShiftEq | LeftBitShiftEq | Not | BitwiseNegate
                | And | Or | Assign | FieldAccess | FunctionCall | Dereference | ImmutableAddressOf
                | MutableAddressOf | As => None,
            },

            Void | Never => None,
        }
    }
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Operation::Not => NOT_TOKEN.to_string(),
            Operation::Neg => SUB_TOKEN.to_string(),
            Operation::BitwiseNegate => BITWISE_NEGATE_TOKEN.to_string(),

            Operation::Plus => ADD_TOKEN.to_string(),
            Operation::Minus => SUB_TOKEN.to_string(),
            Operation::Mul | Operation::Dereference => MUL_TOKEN.to_string(),
            Operation::Exp => format!("{}{}", MUL_TOKEN, MUL_TOKEN),
            Operation::Div => DIV_TOKEN.to_string(),
            Operation::Mod => MOD_TOKEN.to_string(),

            Operation::BitwiseAnd | Operation::ImmutableAddressOf => BITWISE_AND_TOKEN.to_string(),
            Operation::BitwiseOr => BITWISE_OR_TOKEN.to_string(),
            Operation::BitwiseXor => BITWISE_XOR_TOKEN.to_string(),
            Operation::RightBitShift => format!("{}{}", GREATER_THAN_TOKEN, GREATER_THAN_TOKEN),
            Operation::LeftBitShift => format!("{}{}", LESS_THAN_TOKEN, LESS_THAN_TOKEN),

            Operation::Assign => ASSIGNMENT_TOKEN.to_string(),
            Operation::PlusEq => format!("{}{}", ADD_TOKEN, ASSIGNMENT_TOKEN),
            Operation::MinusEq => format!("{}{}", SUB_TOKEN, ASSIGNMENT_TOKEN),
            Operation::MulEq => format!("{}{}", MUL_TOKEN, ASSIGNMENT_TOKEN),
            Operation::ExpEq => format!("{}{}{}", MUL_TOKEN, MUL_TOKEN, ASSIGNMENT_TOKEN),
            Operation::DivEq => format!("{}{}", DIV_TOKEN, ASSIGNMENT_TOKEN),
            Operation::ModEq => format!("{}{}", MOD_TOKEN, ASSIGNMENT_TOKEN),
            Operation::BitwiseAndEq => format!("{}{}", BITWISE_AND_TOKEN, ASSIGNMENT_TOKEN),
            Operation::BitwiseOrEq => format!("{}{}", BITWISE_OR_TOKEN, ASSIGNMENT_TOKEN),
            Operation::BitwiseXorEq => format!("{}{}", BITWISE_XOR_TOKEN, ASSIGNMENT_TOKEN),
            Operation::RightBitShiftEq => {
                format!("{}{}{}", GREATER_THAN_TOKEN, GREATER_THAN_TOKEN, ASSIGNMENT_TOKEN)
            }
            Operation::LeftBitShiftEq => {
                format!("{}{}{}", LESS_THAN_TOKEN, LESS_THAN_TOKEN, ASSIGNMENT_TOKEN)
            }
            Operation::NotEqual => format!("{}{}", NOT_TOKEN, ASSIGNMENT_TOKEN),

            Operation::And => format!("{}{}", BITWISE_AND_TOKEN, BITWISE_AND_TOKEN),
            Operation::Or => format!("{}{}", BITWISE_OR_TOKEN, BITWISE_OR_TOKEN),
            Operation::GreaterThan => GREATER_THAN_TOKEN.to_string(),
            Operation::Geq => format!("{}{}", GREATER_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::LessThan => LESS_THAN_TOKEN.to_string(),
            Operation::Leq => format!("{}{}", LESS_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::Equivalence => format!("{}{}", ASSIGNMENT_TOKEN, ASSIGNMENT_TOKEN),

            Operation::FieldAccess => FIELD_ACCESS_TOKEN.to_string(),
            Operation::FunctionCall => "()".to_string(),
            Operation::MutableAddressOf => "&mut".to_string(),

            Operation::As => AS_KEYWORD.to_string()
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
    Float,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LoopKind {
    For,
    While,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ControlFlowKind {
    Return,
    Break,
    Continue,
    Throw,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum KeywordKind {
    Int,
    Float,
    String,
    Bool,
    Char,
    Never,
    If,
    Else,
    While,
    For,
    Break,
    Continue,
    Return,
    Throw,
    Fn,
    Struct,
    Impl,
    Let,
    Const,
    Enum,
    Public,
    Private,
    SelfKw,
    Trait,
    Type,
    Mut,
    Heap,
    Import,
    From,
    Export,
    Sizeof
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum QualifierKind {
    Public,
    Private,
}

impl std::fmt::Display for QualifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QualifierKind::Public => write!(f, "public"),
            QualifierKind::Private => write!(f, "private"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    Identifier,
    HeapRegion,
    Operator(Operation),
    NumberLiteral(NumberKind),
    BooleanLiteral,
    StringLiteral,
    CharLiteral,
    Keyword(KeywordKind),
    Semicolon,
    OpenParenthesis,
    CloseParenthesis,
    OpenBracket,
    CloseBracket,
    OpenBrace,
    CloseBrace,
    Comma,
    Colon,
    EndOfFile,
}

pub const SYNC_TOKENS: [TokenKind; 16] = [
    TokenKind::Keyword(KeywordKind::If),
    TokenKind::Keyword(KeywordKind::For),
    TokenKind::Keyword(KeywordKind::While),
    TokenKind::Keyword(KeywordKind::Return),
    TokenKind::Keyword(KeywordKind::Break),
    TokenKind::Keyword(KeywordKind::Continue),
    TokenKind::Keyword(KeywordKind::Let),
    TokenKind::Keyword(KeywordKind::Const),
    TokenKind::Keyword(KeywordKind::Fn),
    TokenKind::Keyword(KeywordKind::Struct),
    TokenKind::Keyword(KeywordKind::Enum),
    TokenKind::Keyword(KeywordKind::Impl),
    TokenKind::Keyword(KeywordKind::Trait),
    TokenKind::Keyword(KeywordKind::Type),
    TokenKind::Keyword(KeywordKind::Public),
    TokenKind::Keyword(KeywordKind::Private),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl Default for Position {
    fn default() -> Self {
        Position { line: 1, column: 1 }
    }
}

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
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
        write!(
            f,
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
    fn is_default(self) -> bool {
        self == Span::default()
    }

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

    pub fn get_lines(&self, lines: Rc<Vec<String>>) -> Vec<(String, usize)> {
        if self.is_default() {
            return vec![];
        }

        let mut ret: Vec<(String, usize)> = vec![];

        for i in self.start_pos.line..=self.end_pos.line {
            ret.push((lines[i - 1].clone(), i));
        }

        ret
    }

    pub fn get_all_lines(lines: Rc<Vec<String>>, spans: &[Span]) -> Vec<(String, usize)> {
        let mut ret = vec![];
        for span in spans.iter() {
            ret.extend(span.get_lines(lines.clone()));
        }

        return ret;
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    /// The true value in source.
    value: String,
    /// The type of token.
    token_kind: TokenKind,
    /// Details about the token's placement in source.
    span: Span,
}

impl Token {
    pub fn new(value: String, token_type: TokenKind, span: Span) -> Token {
        Token {
            value,
            token_kind: token_type,
            span,
        }
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

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let token_type_str = match self {
            TokenKind::Identifier => "Identifier".cyan(),
            TokenKind::HeapRegion => "'heap".cyan(),
            TokenKind::Operator(op) => format!("Operator::{:?}", op).bright_magenta(),
            TokenKind::NumberLiteral(n) => format!("Number::{:?}", n).blue(),
            TokenKind::BooleanLiteral => "Boolean".magenta(),
            TokenKind::StringLiteral => "String".green(),
            TokenKind::CharLiteral => "Character".green(),
            TokenKind::Keyword(keyword) => match keyword {
                KeywordKind::Int => "Keyword::Int".cyan(),
                KeywordKind::Float => "Keyword::Float".cyan(),
                KeywordKind::String => "Keyword::String".cyan(),
                KeywordKind::Bool => "Keyword::Bool".cyan(),
                KeywordKind::Char => "Keyword::Char".cyan(),
                KeywordKind::Never => "Keyword::Never".cyan(),
                KeywordKind::If => "Keyword::If".yellow(),
                KeywordKind::Else => "Keyword::Else".yellow(),
                KeywordKind::While => "Keyword::While".yellow(),
                KeywordKind::For => "Keyword::For".yellow(),
                KeywordKind::Break => "Keyword::Break".red(),
                KeywordKind::Continue => "Keyword::Continue".red(),
                KeywordKind::Return => "Keyword::Return".red(),
                KeywordKind::Throw => "Keyword::Throw".red(),
                KeywordKind::Fn => "Keyword::Fn".green(),
                KeywordKind::Struct => "Keyword::Struct".green(),
                KeywordKind::Let => "Keyword::Let".green(),
                KeywordKind::Const => "Keyword::Const".green(),
                KeywordKind::Mut => "Keyword::Mut".green(),
                KeywordKind::Enum => "Keyword::Enum".green(),
                KeywordKind::Public => "Keyword::Public".blue(),
                KeywordKind::Private => "Keyword::Private".blue(),
                KeywordKind::SelfKw => "Keyword::SelfKw".blue(),
                KeywordKind::Impl => "Keyword::Impl".purple(),
                KeywordKind::Trait => "Keyword::Trait".purple(),
                KeywordKind::Type => "Keyword::Type".purple(),
                KeywordKind::Heap => "Keyword::Heap".magenta(),
                KeywordKind::Import => "Keyword::Import".yellow(),
                KeywordKind::From => "Keyword::From".yellow(),
                KeywordKind::Export => "Keyword::Export".yellow(),
                KeywordKind::Sizeof => "Keyword::Sizeof".purple()
            },
            TokenKind::Semicolon => "Semicolon".dimmed(),
            TokenKind::OpenParenthesis => "OpenParen".dimmed(),
            TokenKind::CloseParenthesis => "CloseParen".dimmed(),
            TokenKind::OpenBracket => "OpenBracket".dimmed(),
            TokenKind::CloseBracket => "CloseBracket".dimmed(),
            TokenKind::OpenBrace => "OpenCurly".dimmed(),
            TokenKind::CloseBrace => "CloseCurly".dimmed(),
            TokenKind::Comma => "Comma".dimmed(),
            TokenKind::Colon => "Colon".dimmed(),
            TokenKind::EndOfFile => "<EOF>".into(),
        };

        write!(f, "{}", token_type_str)
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ({}) at [{}]",
            self.value.bold(),
            self.get_token_kind(),
            self.span
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReferenceKind {
    Value,
    Reference,
    MutableReference,
}