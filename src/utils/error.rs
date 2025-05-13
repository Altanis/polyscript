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
    AlreadyDeclared(String)
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
            ErrorKind::AlreadyDeclared(variable) => format!("declared variable {} already exists in scope", variable)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    span: Span,
    source_line: String
}

impl Error {
    pub fn new(kind: ErrorKind, span: Span, source_line: String) -> Error {
        Error {
            kind,
            span,
            source_line
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[{}] {}", "error".red().bold(), self.kind.as_str())?;
        writeln!(f, "as found in [insert_file_here]:{}:{}", self.span.start_pos.line, self.span.start_pos.column)?;

        writeln!(f, "    {}", self.source_line)?;
        writeln!(f, "    {}^{}^", " ".repeat(self.span.start_pos.column - 1), "^".repeat(self.span.end_pos.column - self.span.start_pos.column))?;

        Ok(())
    }
}

impl std::error::Error for Error {}