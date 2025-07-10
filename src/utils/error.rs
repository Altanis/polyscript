use colored::Colorize;

use crate::boxed;

use super::kind::Span;

#[derive(Debug, Clone)]
pub enum ErrorKind {
    UnrecognizedSymbol(String),
    UnexpectedEOF,
    InvalidDigit(String),
    InvalidEscapeSequence(String),
    UnterminatedString,
    InvalidChar(String),
    UnterminatedChar,
    UnexpectedToken(String, String, String),
    UninitializedConstant,
    UnknownIdentifier(String),
    UnresolvedType(String),
    AlreadyDeclared(String),
    UnknownType,
    InvalidImpl(Option<String>),
    ExpectedType,
    InvalidConstraint(String),
    UnimplementedTrait(String, String),
    ConflictingTraitImpl(String, String),
    InvalidTraitImpl(String),
    ConflictingInherentImpl(String),
    InvalidDereference,
    ExpectedScopedItem,
    FieldNotFound(String, String),
    InvalidFieldAccess(String),
    IncorrectFieldAccessRhs,
    BadVariableDeclaration,
    SelfOutsideImpl,
    InvalidThis(&'static str),
    ExpectedIdentifier,
    TypeMismatch(String, String)
    // InvalidOperation()
    // MismatchedTypes(TypeInfo, TypeInfo),
}

impl ErrorKind {
    fn as_str(&self) -> String {
        match self {
            ErrorKind::UnrecognizedSymbol(symbol) => format!("unrecognized symbol {}", symbol),
            ErrorKind::UnexpectedEOF => "unexpected <eof> while parsing".to_string(),
            ErrorKind::InvalidDigit(digit) => format!("invalid digit {}", digit),
            ErrorKind::InvalidEscapeSequence(sequence) => format!("invalid escape sequence {}", sequence),
            ErrorKind::UnterminatedString => "string left unterminated".to_string(),
            ErrorKind::InvalidChar(char) => format!("invalid char {}", char),
            ErrorKind::UnterminatedChar => "unterminated or degenerate char".to_string(),
            ErrorKind::UnexpectedToken(symbol, found, expected) 
                => format!("unexpected token: found \"{}\" of type {}, expected {}", symbol, found, expected),
            ErrorKind::UninitializedConstant => "constant declared but no value assigned".to_string(),
            ErrorKind::UnknownIdentifier(name) => format!("could not find \"{}\" in scope", name),
            ErrorKind::UnresolvedType(name) => format!("type for symbol \"{}\" has not been determined by this line", name),
            ErrorKind::AlreadyDeclared(variable) => format!("attempted to declare {}, but it already exists in scope", variable),
            ErrorKind::UnknownType => "could not determine type of data by this line".to_string(),
            ErrorKind::InvalidImpl(type_ref) 
                => format!("cannot construct impl block for {}", type_ref.as_ref().map_or("an unnamed identifier", |v| v)),
            ErrorKind::ExpectedType => "expected identifier to resolve to a type".to_string(),
            ErrorKind::InvalidConstraint(constraint) => format!("expected constraint to be a trait, instead found \"{}\"", constraint),
            ErrorKind::UnimplementedTrait(tr, ty) => format!("trait {} not implemented for type {}", tr, ty),
            ErrorKind::ConflictingTraitImpl(tr, ty) => format!("conflicting trait implementations for {} on type {}", tr, ty),
            ErrorKind::InvalidTraitImpl(ty) => format!("not all types in trait implemented, missing: {}", ty),
            ErrorKind::ConflictingInherentImpl(ty) => format!("conflicting implementations for type {}", ty),
            ErrorKind::InvalidDereference => "attempted to dereference something that wasn't a pointer".to_string(),
            ErrorKind::ExpectedScopedItem => "expected an item with a scope".to_string(),
            ErrorKind::FieldNotFound(field, type_name) => format!("field \"{}\" not found in type {}", field, type_name),
            ErrorKind::InvalidFieldAccess(type_name) => format!("cannot access field on type {}", type_name),
            ErrorKind::IncorrectFieldAccessRhs => "cannot access this field".to_string(),
            ErrorKind::BadVariableDeclaration => "variable declaration must be annotated with a type or value".to_string(),
            ErrorKind::SelfOutsideImpl => "use of Self outside of an impl block".to_string(),
            ErrorKind::InvalidThis(place) => format!("found \"this\" {}", place),
            ErrorKind::ExpectedIdentifier => "expected an identifier for the rhs of a field access operation".to_string(),
            ErrorKind::TypeMismatch(t1, t2) => format!("types {} and {} are incompatible", t1, t2)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    span: Span,
    source_lines: Vec<(String, usize)>
}

pub type BoxedError = Box<Error>;

impl Error {
    pub fn new(kind: ErrorKind) -> BoxedError {
        boxed!(Error {
            kind,
            span: Span::default(),
            source_lines: vec![]
        })
    }

    pub fn from_one_error(kind: ErrorKind, span: Span, source_line: (String, usize)) -> BoxedError {
        boxed!(Error {
            kind,
            span,
            source_lines: vec![source_line]
        })
    }

    pub fn from_multiple_errors(kind: ErrorKind, span: Span, source_lines: Vec<(String, usize)>) -> BoxedError {
        boxed!(Error {
            kind,
            span,
            source_lines
        })
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[{}] {}", "error".red().bold(), self.kind.as_str())?;
        writeln!(f, "as found in [insert_file_here]:{}:{}", self.span.start_pos.line, self.span.start_pos.column)?;

        let mut used_numbers = vec![];
        for (content, number) in self.source_lines.iter() {
            if used_numbers.contains(number) {
                continue;
            } else {
                used_numbers.push(*number);
            }

            writeln!(f, "    {}", content)?;
            
            if *number == self.span.start_pos.line {
                writeln!(f, "    {}^{}^", " ".repeat(self.span.start_pos.column - 1), "^".repeat(self.span.end_pos.column.saturating_sub(self.span.start_pos.column)))?;
            }
        }

        Ok(())
    }
}

impl std::error::Error for Error {}