use crate::utils::{error::ParserError, token::{Operation, Position, Span, Token, TokenKind}};

use super::ast::{Node, NodeKind};

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
    errors: Vec<ParserError>,
    temp_span: Span
}

impl Parser {
    fn is_at_end(&self) -> bool {
        self.peek().get_token_kind() == TokenKind::EndOfFile
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
    
    fn consume(&mut self, token_type: TokenKind, error_msg: &str) -> Result<&Token, ParserError> {
        if self.check(token_type) {
            Ok(self.advance())
        } else {
            let position = self.peek().get_span().start_pos;
            Err(ParserError::UnexpectedToken(position.line, position.column, format!("{error_msg}, instead found {:?}.", self.peek().get_token_kind())))
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

    fn create_span_from_current_token(&self) -> Span {
        let previous_span = self.peek().get_span();

        Span {
            start: previous_span.start,
            start_pos: previous_span.start_pos,
            end: 0,
            end_pos: Position::default()
        }
    }
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Parser {
        Parser { 
            tokens, 
            current: 0, 
            errors: vec![],
            temp_span: Span::default()
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
                end: self.tokens.last().unwrap().get_span().end,
                start_pos: Position::default(),
                end_pos: Position {
                    line: self.tokens.last().unwrap().get_span().end_pos.line,
                    column: self.tokens.last().unwrap().get_span().end_pos.column,
                }
            },
        }
    }

    fn parse_statement(&mut self) -> Result<Node, ParserError> {
        let token = self.peek();
        match token.get_token_kind() {
            TokenKind::VariableDeclaration(mutable) => self.parse_variable_declaration(mutable),
            _ => todo!()
        }
    }

    fn parse_variable_declaration(&mut self, mutable: bool) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.advance();

        let identifier = self.consume(TokenKind::Identifier, "Expected a variable name")?;
        let name = identifier.get_value().to_string();

        let mut type_annotation = None;
        if self.match_token(TokenKind::Colon) {
            type_annotation = Some(Box::new(self.parse_type()?));
        }

        let mut initializer = None;
        if self.match_token(TokenKind::Binary(Operation::Assign)) {
            initializer = Some(Box::new(self.parse_expression()?));
        }

        self.consume(TokenKind::EndOfLine, "Expected ';' after variable declaration")?;

        Ok(Node {
            kind: NodeKind::VariableDeclaration {
                mutable,
                name,
                type_annotation,
                initializer,
            },
            span: span.set_end_from_span(dbg!(self.previous().get_span()))
        })
    }

    fn parse_type(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        let type_reference = self.consume(TokenKind::Type, "Expected a type annotation")?;
        
        Ok(Node {
            kind: NodeKind::TypeReference(type_reference.get_value().clone()),
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_expression(&mut self) -> Result<Node, ParserError> {
        todo!()
    }
}