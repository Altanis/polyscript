use colored::*;
use std::rc::Rc;

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

pub const COMMENT_TOKEN: char = '#';

pub const INT_TYPE: &str = "int";
pub const FLOAT_TYPE: &str = "float";
pub const BOOL_TYPE: &str = "bool";
pub const STRING_TYPE: &str = "string";
pub const CHAR_TYPE: &str = "char";
pub const NULL_TYPE: &str = "null"; // NOTE: Programs may not use this type.

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
pub const THIS_KEYWORD: &str = "this";
pub const PUBLIC_KEYWORD: &str = "public";
pub const PRIVATE_KEYWORD: &str = "private";
pub const TRAIT_KEYWORD: &str = "trait";
pub const TYPE_KEYWORD: &str = "type";
pub const MUT_KEYWORD: &str = "mut";

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
    Leq, // ≤
    Equivalence, // ==
    NotEqual, // !=

    // CALL
    FieldAccess,

    // POINTER OPS //
    Dereference,
    ImmutableAddressOf,
    MutableAddressOf,
}

impl Operation {
    pub fn is_unary(self) -> bool {
        matches!(
            self,
            Operation::Not
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
    
            Operation::GreaterThan 
            | Operation::Geq 
            | Operation::LessThan 
            | Operation::Leq => (5, 6),
    
            Operation::BitwiseOr => (6, 7),
    
            Operation::BitwiseXor => (7, 8),
    
            Operation::BitwiseAnd => (8, 9),
    
            Operation::Plus 
            | Operation::Minus => (9, 10),
    
            Operation::Mul 
            | Operation::Div 
            | Operation::Mod => (10, 11),
    
            Operation::LeftBitShift 
            | Operation::RightBitShift => (11, 12),
    
            Operation::Exp => (12, 11),
    
            Operation::Not 
            | Operation::BitwiseNegate => (13, 14),

            Operation::FieldAccess => (14, 15),

            Operation::Dereference
            | Operation::ImmutableAddressOf
            | Operation::MutableAddressOf => (15, 16)
        }
    }

    /// Returns the trait name and whether it is a unary or binary operation.
    pub fn to_trait_data(&self) -> (String, bool) {
        match self {
            Operation::Not => ("Not".to_string(), false),
            Operation::BitwiseNegate => ("BitwiseNegate".to_string(), false),
            Operation::Plus => ("Add".to_string(), true),
            Operation::Minus => ("Subtract".to_string(), true),
            Operation::Mul => ("Multiply".to_string(), true),
            Operation::Exp => ("Exponentiate".to_string(), true),
            Operation::Div => ("Divide".to_string(), true),
            Operation::Mod => ("Modulo".to_string(), true),
            Operation::BitwiseAnd => ("BitwiseAnd".to_string(), true),
            Operation::BitwiseOr => ("BitwiseOr".to_string(), true),
            Operation::BitwiseXor => ("BitwiseXor".to_string(), true),
            Operation::RightBitShift => ("RightBitShift".to_string(), true),
            Operation::LeftBitShift => ("LeftBitShift".to_string(), true),
            Operation::Assign => ("Assign".to_string(), true),
            Operation::PlusEq => ("AddAssign".to_string(), true),
            Operation::MinusEq => ("SubtractAssign".to_string(), true),
            Operation::MulEq => ("MultiplyAssign".to_string(), true),
            Operation::ExpEq => ("ExponentiateAssign".to_string(), true),
            Operation::DivEq => ("DivideAssign".to_string(), true),
            Operation::ModEq => ("ModuloAssign".to_string(), true),
            Operation::BitwiseAndEq => ("BitwiseAndAssign".to_string(), true),
            Operation::BitwiseOrEq => ("BitwiseOrAssign".to_string(), true),
            Operation::BitwiseXorEq => ("BitwiseXorAssign".to_string(), true),
            Operation::RightBitShiftEq => ("RightBitShiftAssign".to_string(), true),
            Operation::LeftBitShiftEq => ("LeftBitShiftAssign".to_string(), true),
            Operation::NotEqual => ("NotEqual".to_string(), true),
            Operation::And => ("And".to_string(), true),
            Operation::Or => ("Or".to_string(), true),
            Operation::GreaterThan => ("GreaterThan".to_string(), true),
            Operation::Geq => ("GreaterThanOrEqual".to_string(), true),
            Operation::LessThan => ("LessThan".to_string(), true),
            Operation::Leq => ("LessThanOrEqual".to_string(), true),
            Operation::Equivalence => ("Equivalence".to_string(), true),
            Operation::FieldAccess => ("FieldAccess".to_string(), true),
            Operation::Dereference => ("Dereference".to_string(), false),
            Operation::ImmutableAddressOf => ("ImmutableAddressOf".to_string(), false),
            Operation::MutableAddressOf => ("MutableAddressOf".to_string(), false)
        }
    }
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Operation::Not => NOT_TOKEN.to_string(),
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
            Operation::RightBitShiftEq => format!("{}{}{}", GREATER_THAN_TOKEN, GREATER_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::LeftBitShiftEq => format!("{}{}{}", LESS_THAN_TOKEN, LESS_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::NotEqual => format!("{}{}", NOT_TOKEN, ASSIGNMENT_TOKEN),

            Operation::And => format!("{}{}", BITWISE_AND_TOKEN, BITWISE_AND_TOKEN),
            Operation::Or => format!("{}{}", BITWISE_OR_TOKEN, BITWISE_OR_TOKEN),
            Operation::GreaterThan => GREATER_THAN_TOKEN.to_string(),
            Operation::Geq => format!("{}{}", GREATER_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::LessThan => LESS_THAN_TOKEN.to_string(),
            Operation::Leq => format!("{}{}", LESS_THAN_TOKEN, ASSIGNMENT_TOKEN),
            Operation::Equivalence => format!("{}{}", ASSIGNMENT_TOKEN, ASSIGNMENT_TOKEN),

            Operation::FieldAccess => FIELD_ACCESS_TOKEN.to_string(),
            Operation::MutableAddressOf => "&mut".to_string()
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
pub enum KeywordKind {
    Int,
    Float,
    String,
    Bool,
    Char,
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
    This,
    Trait,
    Type,
    Mut
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum QualifierKind {
    Public,
    Private
}

impl std::fmt::Display for QualifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QualifierKind::Public => write!(f, "public"),
            QualifierKind::Private => write!(f, "private")
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    Identifier,
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

    pub fn get_lines(&self, lines: Rc<Vec<String>>) -> Vec<(String, usize)> {
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

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let token_type_str = match self {
            TokenKind::Identifier => "Identifier".cyan(),
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
                KeywordKind::This => "Keyword::This".blue(),
                KeywordKind::Impl => "Keyword::Impl".purple(),
                KeywordKind::Trait => "Keyword::Trait".purple(),
                KeywordKind::Type => "Keyword::Type".purple()
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
            TokenKind::EndOfFile => "<EOF>".into()
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
    MutableReference
}