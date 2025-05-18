use std::{collections::HashMap, rc::Rc};

use colored::*;

use super::error::{Error, ErrorKind};

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
pub const THROW_KEYWORD: &str = "throw";
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operation {
    // UNARY
    Not, // !
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
    NotEqual,

    // CONDITIONAL
    And,
    Or,
    GreaterThan,
    Geq, // ≥
    LessThan,
    Leq, // ≤
    Equivalence,

    // CALL
    FieldAccess,

    // POINTER OPS //
    Dereference,
    ImmutableAddressOf,
    MutableAddressOf,
}

impl Operation {
    pub fn is_postfix(self) -> bool {
        matches!(self, Operation::Increment | Operation::Decrement)
    }

    pub fn is_unary(self) -> bool {
        matches!(
            self,
            Operation::Not
                | Operation::BitwiseNegate
                | Operation::Increment
                | Operation::Decrement
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
            | Operation::BitwiseNegate 
            | Operation::Increment 
            | Operation::Decrement => (13, 14),

            Operation::FieldAccess => (14, 15),

            Operation::Dereference
            | Operation::ImmutableAddressOf
            | Operation::MutableAddressOf => (15, 16)
        }
    }
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Operation::Not => NOT_TOKEN.to_string(),
            Operation::BitwiseNegate => BITWISE_NEGATE_TOKEN.to_string(),
            Operation::Increment => format!("{}{}", ADD_TOKEN, ADD_TOKEN),
            Operation::Decrement => format!("{}{}", SUB_TOKEN, SUB_TOKEN),

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

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable,
    Function,
    Struct,
    Trait,
    Enum,
    TypeAlias,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub type_info: TypeInfo,
    pub mutable: bool,
    pub span: Span,
    pub public: Option<bool>,
    pub generic_parameters: Vec<TypeInfo>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeInfo {
    pub base_type: String,
    pub generic_parameters: Vec<TypeInfo>,
    pub function_data: Option<FunctionTypeData>,
    pub reference_kind: ReferenceKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionTypeData {
    pub params: Vec<TypeInfo>,
    pub return_type: Box<TypeInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReferenceKind {
    Value,
    Reference,
    MutableReference,
}

impl TypeInfo {
    pub fn new(base_type: impl Into<String>, generic_parameters: Vec<TypeInfo>, reference_kind: ReferenceKind) -> Self {
        Self {
            base_type: base_type.into(),
            generic_parameters,
            function_data: None,
            reference_kind,
        }
    }

    pub fn from_function_expression(generic_parameters: Vec<TypeInfo>, function_data: FunctionTypeData, reference_kind: ReferenceKind) -> Self {
        Self {
            base_type: String::new(),
            generic_parameters,
            function_data: Some(function_data),
            reference_kind,
        }
    }
}

pub struct SymbolTable {
    scopes: Vec<HashMap<String, Symbol>>,
    lines: Rc<Vec<String>>,
}

impl SymbolTable {
    pub fn new(lines: Rc<Vec<String>>) -> Self {
        Self {
            scopes: vec![HashMap::new()],
            lines,
        }
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn find_symbol(&self, name: &str) -> Option<&Symbol> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
    }

    pub fn add_symbol(&mut self, symbol: Symbol) -> Result<(), Box<Error>> {
        if let Some(existing) = self.current_scope().get(&symbol.name) {
            return Err(Error::from_multiple_errors(
                ErrorKind::AlreadyDeclared(symbol.name),
                symbol.span,
                Span::get_all_lines(self.lines.clone(), &[existing.span, symbol.span]),
            ));
        }

        self.current_scope_mut()
            .insert(symbol.name.clone(), symbol);
        Ok(())
    }

    fn current_scope(&self) -> &HashMap<String, Symbol> {
        self.scopes.last().expect("Always at least one scope")
    }

    fn current_scope_mut(&mut self) -> &mut HashMap<String, Symbol> {
        self.scopes.last_mut().expect("Always at least one scope")
    }
}

impl std::fmt::Display for SymbolKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let colored = match self {
            SymbolKind::Variable => "Variable".green(),
            SymbolKind::Function => "Function".blue(),
            SymbolKind::Struct => "Struct".magenta(),
            SymbolKind::Trait => "Trait".cyan(),
            SymbolKind::Enum => "Enum".yellow(),
            SymbolKind::TypeAlias => "TypeAlias".white(),
        };
        write!(f, "{}", colored)
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.cyan().bold())?;
        write!(f, " ({})", self.kind)?;
        write!(f, " : {}", self.type_info)?;
        
        if self.mutable {
            write!(f, " {}", "mut".red())?;
        }

        if self.public == Some(true) {
            write!(f, " {}", "pub".purple())?;
        }
        
        if !self.generic_parameters.is_empty() {
            let generics = self.generic_parameters.iter()
                .map(|g| g.to_string().dimmed().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, " <{}>", generics)?;
        }
        
        Ok(())
    }
}

impl std::fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let reference = match self.reference_kind {
            ReferenceKind::Value => "".normal(),
            ReferenceKind::Reference => "&".red(),
            ReferenceKind::MutableReference => "&mut ".red().bold(),
        };

        if let Some(func_data) = &self.function_data {
            return write!(f, "{}{}", reference, func_data);
        }

        let base = self.base_type.yellow().bold();
        let generics = if !self.generic_parameters.is_empty() {
            format!("<{}>", 
                self.generic_parameters.iter()
                    .map(|g| g.to_string().blue().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            String::new()
        };

        write!(f, "{}{}{}", reference, base, generics)
    }
}

impl std::fmt::Display for FunctionTypeData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self.params.iter()
            .map(|p| p.to_string().green().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let return_type = self.return_type.to_string().magenta();
        write!(f, "({}) -> {}", params, return_type)
    }
}

fn display_scopes(scopes: &[HashMap<String, Symbol>], indent: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if scopes.is_empty() {
        return Ok(());
    }

    for symbol in scopes[0].values() {
        writeln!(f, "{:indent$}{}", "", symbol, indent = indent)?;
    }
    
    if scopes.len() > 1 {
        writeln!(f, "{:indent$}{{", "", indent = indent)?;
        display_scopes(&scopes[1..], indent + 4, f)?;
        writeln!(f, "{:indent$}}}", "", indent = indent)?;
    }

    Ok(())
}

impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_scopes(&self.scopes, 0, f)
    }
}