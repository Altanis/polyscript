use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum LexerError {
    #[error("[LEXER_ERROR / UNIDENTIFIED_ERROR] ({0}:{1}): Unrecognized symbol {2}.")]
    UnidentifiedError(usize, usize, String),
    #[error("[LEXER_ERROR / UNEXPECTED_EOF] ({0}:{1}): Unexpected end of file while reading token.")]
    UnexpectedEOF(usize, usize),
    #[error("[LEXER_ERROR / INVALID_DIGIT] ({0}:{1}): Unexpected digit {2} in a numeric literal.")]
    InvalidDigit(usize, usize, char),
    #[error("[LEXER_ERROR / INVALID_ESCAPE_SEQUENCE] ({0}:{1}): Escape sequence {2} is not valid.")]
    InvalidEscapeSequence(usize, usize, String),
    #[error("[LEXER_ERROR / UNTERMINATED_STRING] ({0}:{1}): String literal has no ending quote.")]
    UnterminatedString(usize, usize),
    #[error("[LEXER_ERROR / INVALID_CHAR] ({0}:{1}): Characters must not be empty nor have more than one character.")]
    InvalidChar(usize, usize),
    #[error("[LEXER_ERROR / UNTERMINATED_CHAR] ({0}:{1}): Char literal has no ending quote.")]
    UnterminatedChar(usize, usize),
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParserError {
    #[error("[PARSER_ERROR / UNEXPECTED_TOKEN] ({0}:{1}): {2}")]
    UnexpectedToken(usize, usize, String)
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum RuntimeError {
    
}