use crate::utils::{error::ParserError, token::{Token, TokenKind, Span}};

use super::ast::{Node, NodeKind};

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
    errors: Vec<ParserError>
}

impl Parser {
    fn is_at_end(&self) -> bool {
        self.peek().get_token_kind() == TokenKind::EOF
    }
    
    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }
    
    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.current += 1;
        }

        self.previous()
    }

    fn check(&self, token_type: TokenKind) -> bool {
        if self.is_at_end() {
            return false;
        }

        matches!(&self.peek().get_token_kind(), t if std::mem::discriminant(t) == std::mem::discriminant(&token_type))
    }
    
    fn match_token(&mut self, token_type: TokenKind) -> bool {
        if self.check(token_type) {
            self.advance();
            true
        } else {
            false
        }
    }
    
    fn consume(&mut self, token_type: TokenKind, error_msg: &str) -> Result<&Token, String> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            Err(format!("{} Found {:?}", error_msg, self.peek().get_token_kind()))
        }
    }

    fn generate_span(&mut self) -> Span {
        Span::default()
    }
}

impl Parser {

}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        Parser { 
            tokens, 
            current: 0, 
            errors: vec![]
        }
    }

    pub fn parse(&mut self) -> Result<Node, Vec<ParserError>> {
        let program = self.parse_program();
        if self.errors.is_empty() {
            Ok(program)
        } else {
            Err(self.errors.clone())
        }
    }

    fn parse_program(&mut self) -> Node {
        let mut statements = vec![];

        while !self.is_at_end() {
            match self.parse_statement() {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.errors.push(err);
                    self.synchronize();
                }
            }
        }

        Node {
            kind: NodeKind::Program(statements),
            span: Span {
                start: 0,
                end: self.tokens.len(),
                line: 0,
                column: 0,
            },
        }
    }

    fn parse_statement(&mut self) -> Result<Node, ParserError> {
        let token = self.peek();
        match token.get_token_kind() {

            _ => todo!()
        }
    }

    fn synchronize(&mut self) {
        self.advance();
        
        while !self.is_at_end() {
            if self.previous().get_token_kind() == TokenKind::EndOfLine {
                return;
            }
            
            match self.peek().get_token_kind() {
                TokenKind::VariableDeclaration(_) |
                TokenKind::FunctionDeclaration |
                TokenKind::ClassDeclaration |
                TokenKind::If |
                TokenKind::Loop(_) => return,
                _ => {},
            }
            
            self.advance();
        }
    }
}