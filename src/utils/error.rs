use colored::Colorize;

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
    UnknownVariable(String),
    UnresolvedType(String),
    AlreadyDeclared(String),
    UnknownType,
    // InvalidOperation()
    // MismatchedTypes(TypeInfo, TypeInfo),
    // BadVariableDeclaration
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
            ErrorKind::UnknownVariable(name) => format!("could not find variable \"{}\" in scope", name),
            ErrorKind::UnresolvedType(name) => format!("type for symbol \"{}\" has not been determined by this line", name),
            ErrorKind::AlreadyDeclared(variable) => format!("attempted to declare {}, but it already exists in scope", variable),
            ErrorKind::UnknownType => "could not determine type of data at compile-time".to_string(),
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
        Box::new(Error {
            kind,
            span: Span::default(),
            source_lines: vec![]
        })
    }

    pub fn from_one_error(kind: ErrorKind, span: Span, source_line: (String, usize)) -> BoxedError {
        Box::new(Error {
            kind,
            span,
            source_lines: vec![source_line]
        })
    }

    pub fn from_multiple_errors(kind: ErrorKind, span: Span, source_lines: Vec<(String, usize)>) -> BoxedError {
        Box::new(Error {
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