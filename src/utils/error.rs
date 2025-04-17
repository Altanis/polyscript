use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum LexerError {
    #[error("LexerError ({0}:{1}): Unexpected token {2}.")]
    UnidentifiedError(usize, usize, String),
    #[error("LexerError ({0}:{1}): Unexpected end of file while reading token.")]
    UnexpectedEOF(usize, usize),
    #[error("LexerError ({0}:{1}): Unexpected digit {2} in a numeric literal.")]
    InvalidDigit(usize, usize, char)
}

#[derive(Error, Debug, Clone)]
pub enum ParserError {

}

#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    
}