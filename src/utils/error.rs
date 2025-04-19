use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum LexerError {
    #[error("[LEXER_ERROR / UNIDENTIFIED_ERROR] ({0}:{1}): Unrecognized symbol {2}.")]
    UnidentifiedError(usize, usize, String),
    #[error("[LEXER_ERROR / UNEXPECTED_EOF] ({0}:{1}): Unexpected end of file while reading token.")]
    UnexpectedEOF(usize, usize),
    #[error("[LEXER_ERROR / INVALID_DIGIT] ({0}:{1}): Unexpected digit {2} in a numeric literal.")]
    InvalidDigit(usize, usize, char)
}

#[derive(Error, Debug, Clone)]
pub enum ParserError {
    #[error("[PARSER_ERROR / UNEXPECTED_TOKEN] ({0}:{1}): {2}.")]
    UnexpectedToken(usize, usize, String)
}

#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    
}