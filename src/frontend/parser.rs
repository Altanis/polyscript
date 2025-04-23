use crate::utils::{error::ParserError, token::{Operation, Position, Span, Token, TokenKind}};

use super::ast::{FunctionParameter, Node, NodeKind};

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
enum Precedence {
    Assignment   = 1,   // =
    Or           = 2,   // ||
    And          = 3,   // &&
    Equality     = 4,   // == !=
    Comparison   = 5,   // < > <= >=
    BitwiseOr    = 6,   // |
    BitwiseXor   = 7,   // ^
    BitwiseAnd   = 8,   // &
    Term         = 9,   // + -
    Factor       = 10,  // * / %
    Shift        = 11,  // << >>
    Exponent     = 12,  // **
    Unary        = 13,  // - ! ~
    Call         = 14,  // function call, property access, etc.
}

impl From<u8> for Precedence {
    fn from(n: u8) -> Precedence {
        match n {
            1  => Precedence::Assignment,
            2  => Precedence::Or,
            3  => Precedence::And,
            4  => Precedence::Equality,
            5  => Precedence::Comparison,
            6  => Precedence::BitwiseOr,
            7  => Precedence::BitwiseXor,
            8  => Precedence::BitwiseAnd,
            9  => Precedence::Term,
            10 => Precedence::Factor,
            11 => Precedence::Shift,
            12 => Precedence::Exponent,
            13 => Precedence::Unary,
            _  => Precedence::Call,
        }
    }
}

fn binding_power(op: Operation) -> Option<(u8, u8)> {
    match op {
        Operation::Assign => Some((1, 2)), // Assignment
        Operation::Or => Some((2, 3)), // Or
        Operation::And => Some((3, 4)), // And
        Operation::Equivalence => Some((4, 5)), // Equality
        Operation::GreaterThan | Operation::Geq | Operation::LessThan | Operation::Leq => Some((5, 6)), // Comparison
        Operation::BitwiseOr => Some((6, 7)), // BitwiseOr
        Operation::BitwiseXor => Some((7, 8)), // BitwiseXor
        Operation::BitwiseAnd => Some((8, 9)), // BitwiseAnd
        Operation::LeftBitShift | Operation::RightBitShift => Some((11, 12)), // Shift
        Operation::Plus | Operation::Minus => Some((9, 10)), // Term
        Operation::Mul | Operation::Div | Operation::Mod => Some((10, 11)), // Factor
        Operation::Exp => Some((12, 11)), // Exponent
        _ => None,
    }
}

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
    errors: Vec<ParserError>
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
    
    fn match_token(&mut self, token_type: TokenKind) -> bool {
        if self.peek().get_token_kind() == token_type {
            self.advance();
            true
        } else {
            false
        }
    }
    
    fn consume(&mut self, token_type: TokenKind) -> Result<&Token, ParserError> {
        if self.peek().get_token_kind() == token_type {
            Ok(self.advance())
        } else {
            let position = self.peek().get_span().start_pos;
            Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected {:?}, instead found {:?}.", token_type, self.peek().get_token_kind())))
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
    fn parse_expression(&mut self) -> Result<Node, ParserError> {
        self.parse_precedence(Precedence::Assignment)
    }

    fn parse_precedence(&mut self, precedence: Precedence) -> Result<Node, ParserError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            match self.peek().get_token_kind() {
                TokenKind::Operator(operator) if operator.is_postfix() => {
                    lhs = Node {
                        span: lhs.span.set_end_from_span(self.peek().get_span()),
                        kind: NodeKind::UnaryOperation {
                            operator,
                            operand: Box::new(lhs),
                            prefix: false
                        }
                    };

                    self.advance();
                },
                _ => {},
            };

            let token = self.peek().clone(); // todo get rid of clone
            let operator = match token.get_token_kind() {
                TokenKind::Operator(op) => op,
                _ => break,
            };

            let (left_bp, right_bp) = match binding_power(operator) {
                Some((l, r)) => (Precedence::from(l), Precedence::from(r)),
                None => break,
            };
    
            if left_bp < precedence {
                break;
            }
    
            self.advance();
            let rhs = self.parse_precedence(right_bp)?;

            lhs = Node {
                span: lhs.span.set_end_from_span(rhs.span),
                kind: match token.get_token_kind() {
                    TokenKind::Operator(op) => {
                        if op.is_conditional() {
                            NodeKind::ConditionalOperation {
                                operator,
                                left: Box::new(lhs),
                                right: Box::new(rhs),
                            }
                        } else {
                            NodeKind::BinaryOperation {
                                operator,
                                left: Box::new(lhs),
                                right: Box::new(rhs),
                            }
                        }
                    },
                    _ => unreachable!()
                }
            };
        }

        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<Node, ParserError> {
        let token = self.peek();
        let span = self.create_span_from_current_token();

        match token.get_token_kind() {
            TokenKind::Operator(operator) => {
                if !operator.is_unary() {
                    let pos = token.get_span().start_pos;
                    return Err(ParserError::UnexpectedToken(pos.line, pos.column, "Unexpected token in expression".into()));
                }

                let _ = self.advance();
                let operand = Box::new(self.parse_precedence(Precedence::Unary)?);

                Ok(Node {
                    span: span.set_end_from_span(operand.span),
                    kind: NodeKind::UnaryOperation { 
                        operator, 
                        operand,
                        prefix: true
                    },
                })
            },
            TokenKind::Numeric(_) => {
                let token = self.advance();
                let value = token.get_value().parse::<f64>().unwrap(); // TODO: handle numeric types properly

                Ok(Node {
                    kind: NodeKind::FloatLiteral(value),
                    span: token.get_span(),
                })
            },
            TokenKind::Identifier => {
                let token = self.advance();

                Ok(Node {
                    kind: NodeKind::Identifier(token.get_value().clone()),
                    span: token.get_span(),
                })
            },
            TokenKind::OpenParenthesis => {
                self.advance();
                let expr = self.parse_expression()?;
                self.consume(TokenKind::CloseParenthesis)?;
                Ok(expr)
            },
            _ => {
                let pos = token.get_span().start_pos;
                Err(ParserError::UnexpectedToken(pos.line, pos.column, "Unexpected token in expression".into()))
            }
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Node, ParserError> {
        let node = self.parse_expression()?;
        self.consume(TokenKind::EndOfLine)?;
        Ok(node)
    }
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
            TokenKind::FunctionDeclaration => self.parse_function_declaration(),
            TokenKind::If => self.parse_selection_statements(),
            TokenKind::OpenCurlyBracket => self.parse_block(),
            _ => self.parse_expression_statement()
        }
    }

    fn parse_block(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.consume(TokenKind::OpenCurlyBracket)?;
        
        let mut statements = vec![];
    
        while self.peek().get_token_kind() != TokenKind::CloseCurlyBracket {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }
    
        self.consume(TokenKind::CloseCurlyBracket)?;

        Ok(Node {
            kind: NodeKind::Block(statements),
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_variable_declaration(&mut self, mutable: bool) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.consume(TokenKind::VariableDeclaration(mutable))?;

        let var_name = self.consume(TokenKind::Identifier)?.get_value().to_string();

        let mut type_annotation = None;
        if self.match_token(TokenKind::Colon) {
            type_annotation = Some(Box::new(self.parse_type()?));
        }

        let mut initializer = None;
        if self.match_token(TokenKind::Operator(Operation::Assign)) {
            initializer = Some(Box::new(self.parse_expression()?));
        }

        self.consume(TokenKind::EndOfLine)?;

        Ok(Node {
            kind: NodeKind::VariableDeclaration {
                mutable,
                name: var_name,
                type_annotation,
                initializer,
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_type(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        let type_reference = self.advance();
        match type_reference.get_token_kind() {
            TokenKind::Type(value_type) => {
                Ok(Node {
                    kind: NodeKind::TypeReference(value_type),
                    span: span.set_end_from_span(self.previous().get_span())
                })
            },
            _ => {
                let position = type_reference.get_span().end_pos;
                Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected a type reference, instead found {:?}.", type_reference.get_token_kind())))
            }
        }
    }

    fn parse_function_declaration(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.consume(TokenKind::FunctionDeclaration)?;

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();

        let parameters = self.parse_parameter_list()?;

        let mut return_type = None;
        if self.peek().get_token_kind() == TokenKind::Colon {
            self.consume(TokenKind::Colon)?;
            return_type = Some(Box::new(self.parse_type()?));
        }

        let body = Box::new(self.parse_block()?);

        Ok(Node {
            kind: NodeKind::FunctionDeclaration {
                name,
                parameters,
                return_type,
                body
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_parameter_list(&mut self) -> Result<Vec<FunctionParameter>, ParserError> {
        let mut parameters = vec![];

        self.consume(TokenKind::OpenParenthesis)?;
        loop {
            let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
            self.consume(TokenKind::Colon)?;
            let type_annotation = self.parse_type()?;
            let mut default_value = None;

            if self.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                self.consume(TokenKind::Operator(Operation::Assign))?;
                default_value = Some(self.parse_expression()?);
            }

            parameters.push(FunctionParameter {
                name,
                type_annotation,
                default_value
            });

            if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
                break;
            } else {
                self.consume(TokenKind::Comma)?;
            }
        }
        self.consume(TokenKind::CloseParenthesis)?;

        Ok(parameters)
    }

    fn parse_selection_statements(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        
        self.consume(TokenKind::If)?;
        let condition = Box::new(self.parse_expression()?);
        let then_branch = Box::new(self.parse_block()?);
        let mut else_if_branches = vec![];

        let mut else_branch = None;

        while self.peek().get_token_kind() == TokenKind::Else {
            self.consume(TokenKind::Else)?;

            if self.peek().get_token_kind() == TokenKind::If {
                self.consume(TokenKind::If)?;
                let condition = Box::new(self.parse_expression()?);
                let then_branch = Box::new(self.parse_block()?);

                else_if_branches.push((condition, then_branch));
            } else {
                else_branch = Some(Box::new(self.parse_block()?));
            }
        }

        Ok(Node {
            kind: NodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }
}