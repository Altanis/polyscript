use crate::utils::{error::ParserError, kind::{KeywordKind, Operation, Position, QualifierKind, Span, Token, TokenKind, SYNC_TOKENS}};

use super::ast::{Node, NodeKind};

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
            if self.previous().get_token_kind() == TokenKind::Semicolon {
                return;
            }
            
            if SYNC_TOKENS.contains(&self.peek().get_token_kind()) {
                return;
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

            let (left_bp, right_bp) = operator.binding_power();
            let (left_precedence, right_precedence) = (Precedence::from(left_bp), Precedence::from(right_bp));
    
            if left_precedence < precedence {
                break;
            }
    
            self.advance();
            let rhs = self.parse_precedence(right_precedence)?;

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
                    return Err(ParserError::UnexpectedToken(pos.line, pos.column, format!("Unexpected token {:?}.", token.get_token_kind())));
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
            TokenKind::NumberLiteral(_) => {
                let token = self.advance();
                let value = token.get_value().parse::<f64>().unwrap(); // TODO: handle numeric types properly

                Ok(Node {
                    kind: NodeKind::FloatLiteral(value),
                    span: token.get_span(),
                })
            },
            TokenKind::BooleanLiteral => {
                let token = self.advance();
                let value = token.get_value().parse::<bool>().unwrap();

                Ok(Node {
                    kind: NodeKind::BooleanLiteral(value),
                    span: token.get_span(),
                })
            },
            TokenKind::StringLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].to_string();

                Ok(Node {
                    kind: NodeKind::StringLiteral(value),
                    span: token.get_span(),
                })
            },
            TokenKind::CharLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].chars().next().unwrap();

                Ok(Node {
                    kind: NodeKind::CharLiteral(value),
                    span: token.get_span(),
                })
            },
            TokenKind::Identifier => {
                let token = self.advance();
                let name = token.get_value().to_string();
                let span = token.get_span();

                if self.peek().get_token_kind() == TokenKind::OpenBrace {
                    let mut fields = vec![];

                    self.advance();
                    loop {
                        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
                        self.consume(TokenKind::Colon)?;
                        let value = self.parse_expression()?;

                        fields.push((name, value));
                        
                        if self.peek().get_token_kind() == TokenKind::CloseBrace {
                            break;
                        } else {
                            self.consume(TokenKind::Comma)?;
                        }
                    }
                    self.advance();

                    Ok(Node {
                        kind: NodeKind::StructLiteral {
                            name,
                            fields
                        },
                        span: span.set_end_from_span(self.previous().get_span())
                    })
                } else {
                    Ok(Node {
                        kind: NodeKind::Identifier(name),
                        span,
                    })
                }
            },
            TokenKind::OpenParenthesis => {
                self.advance();
                let expr = self.parse_expression()?;
                self.consume(TokenKind::CloseParenthesis)?;
                Ok(expr)
            },
            _ => {
                let pos = token.get_span().start_pos;
                Err(ParserError::UnexpectedToken(pos.line, pos.column, format!("Unexpected token {:?}.", token.get_token_kind())))
            }
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Node, ParserError> {
        let node = self.parse_expression()?;
        self.consume(TokenKind::Semicolon)?;
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
            TokenKind::Keyword(kind) => self.parse_keyword(kind),
            TokenKind::OpenBrace => self.parse_block(),
            _ => self.parse_expression_statement()
        }
    }

    fn parse_keyword(&mut self, kind: KeywordKind) -> Result<Node, ParserError> {
        match kind {
            KeywordKind::Let => self.parse_variable_declaration(true),
            KeywordKind::Const => self.parse_variable_declaration(false),
            KeywordKind::Fn => self.parse_function_declaration(),
            KeywordKind::If => self.parse_selection_statements(),
            KeywordKind::While => self.parse_while_loop(),
            KeywordKind::For => self.parse_for_loop(),
            KeywordKind::Struct => self.parse_struct_declaration(),
            KeywordKind::Return => self.parse_return_statement(),
            KeywordKind::Break => self.parse_break_statement(),
            KeywordKind::Continue => self.parse_continue_statement(),
            KeywordKind::Throw => self.parse_throw_statement(),
            _ => self.parse_expression_statement()
        }
    }

    fn parse_block(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.consume(TokenKind::OpenBrace)?;
        
        let mut statements = vec![];
    
        while self.peek().get_token_kind() != TokenKind::CloseBrace {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }
    
        self.consume(TokenKind::CloseBrace)?;

        Ok(Node {
            kind: NodeKind::Block(statements),
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_variable_declaration(&mut self, mutable: bool) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.advance();

        let var_name = self.consume(TokenKind::Identifier)?.get_value().to_string();

        let mut type_annotation = None;
        if self.match_token(TokenKind::Colon) {
            type_annotation = Some(Box::new(self.parse_type()?));
        }

        let mut initializer = None;
        if self.match_token(TokenKind::Operator(Operation::Assign)) {
            initializer = Some(Box::new(self.parse_expression()?));
        }

        self.consume(TokenKind::Semicolon)?;

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
            TokenKind::Identifier 
                | TokenKind::Keyword(KeywordKind::Int)
                | TokenKind::Keyword(KeywordKind::Float)
                | TokenKind::Keyword(KeywordKind::String)
                | TokenKind::Keyword(KeywordKind::Bool)
                | TokenKind::Keyword(KeywordKind::Void) 
            => {
                Ok(Node {
                    kind: NodeKind::TypeReference(type_reference.get_value().to_string()),
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

        self.advance();

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

    fn parse_parameter_list(&mut self) -> Result<Vec<Node>, ParserError> {
        let mut parameters = vec![];

        self.consume(TokenKind::OpenParenthesis)?;
        if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
            self.consume(TokenKind::CloseParenthesis)?;
            return Ok(parameters);
        }
    
        loop {
            let span = self.create_span_from_current_token();

            let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
            self.consume(TokenKind::Colon)?;
            let type_annotation = Box::new(self.parse_type()?);
            let mut initializer = None;

            if self.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                self.advance();
                initializer = Some(Box::new(self.parse_expression()?));
            }

            parameters.push(Node {
                kind: NodeKind::FunctionParameter {
                    name,
                    type_annotation,
                    initializer
                },
                span: span.set_end_from_span(self.previous().get_span())
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
        
        self.advance();
        let condition = Box::new(self.parse_expression()?);
        let then_branch = Box::new(self.parse_block()?);
        let mut else_if_branches = vec![];

        let mut else_branch = None;

        while self.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Else) {
            self.advance();

            if self.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::If) {
                self.advance();
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

    fn parse_while_loop(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.advance();

        let condition = Box::new(self.parse_expression()?);
        let body = Box::new(self.parse_block()?);

        Ok(Node {
            kind: NodeKind::WhileLoop {
                body,
                condition
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_for_loop(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
    
        self.advance();
        self.consume(TokenKind::OpenParenthesis)?;
    
        let initializer = if self.peek().get_token_kind() == TokenKind::Semicolon {
            self.consume(TokenKind::Semicolon)?;
            None
        } else {
            let init = match self.peek().get_token_kind() {
                TokenKind::Keyword(KeywordKind::Let) => self.parse_variable_declaration(true),
                TokenKind::Keyword(KeywordKind::Const) => self.parse_variable_declaration(false),
                _ => self.parse_expression_statement(),
            }?;
            Some(Box::new(init))
        };
    
        let condition = if self.peek().get_token_kind() == TokenKind::Semicolon {
            self.consume(TokenKind::Semicolon)?;
            None
        } else {
            let cond = self.parse_expression()?;
            self.consume(TokenKind::Semicolon)?;
            Some(Box::new(cond))
        };
    
        let increment = if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
            None
        } else {
            Some(Box::new(self.parse_expression()?))
        };
    
        self.consume(TokenKind::CloseParenthesis)?;
        let body = Box::new(self.parse_block()?);
    
        Ok(Node {
            kind: NodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_return_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.advance();

        let expression = if self.peek().get_token_kind() != TokenKind::Semicolon {
            Some(Box::new(self.parse_expression_statement()?))
        } else {
            self.advance();
            None
        };

        Ok(Node {
            kind: NodeKind::Return(expression),
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_throw_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.advance();

        let expression = Box::new(self.parse_expression_statement()?);

        Ok(Node {
            kind: NodeKind::Throw(expression),
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_continue_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        
        self.advance();
        self.consume(TokenKind::Semicolon)?;

        Ok(Node {
            kind: NodeKind::Continue,
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_break_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        
        self.advance();
        self.consume(TokenKind::Semicolon)?;

        Ok(Node {
            kind: NodeKind::Break,
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_struct_declaration(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        self.advance();

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        let mut fields = vec![];

        self.consume(TokenKind::OpenBrace)?;
        while self.peek().get_token_kind() != TokenKind::CloseBrace {
            fields.push(self.parse_struct_field()?);
        }
        self.consume(TokenKind::CloseBrace)?;

        Ok(Node {
            kind: NodeKind::StructDeclaration {
                name,
                fields
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_struct_field(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        let qualifier_token = self.advance();
        let qualifier = match qualifier_token.get_token_kind() {
            TokenKind::Keyword(KeywordKind::Public) => QualifierKind::Public,
            TokenKind::Keyword(KeywordKind::Private) => QualifierKind::Private,
            _ => {
                let position = qualifier_token.get_span().end_pos;
                return Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected a type reference, instead found {:?}.", qualifier_token.get_token_kind())));
            }
        };

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        self.consume(TokenKind::Colon)?;
        let type_annotation = Box::new(self.parse_type()?);
        self.consume(TokenKind::Semicolon)?;

        Ok(Node {
            kind: NodeKind::StructField {
                qualifier,
                name,
                type_annotation
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    // fn parse_class_declaration(&mut self) -> Result<Node, ParserError> {
    //     let span = self.create_span_from_current_token();
    //     self.advance();

    //     let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        
    //     let mut parent = None;
    //     if self.peek().get_token_kind() == TokenKind::Colon {
    //         self.advance();
    //         parent = Some(Box::new(self.parse_type()?));
    //     }

    //     self.consume(TokenKind::OpenCurlyBracket)?;

    //     let mut methods = vec![];
    //     let mut fields = vec![];

    //     while self.peek().get_token_kind() != TokenKind::CloseCurlyBracket {
    //         let span = self.create_span_from_current_token();

    //         let qualifier = match self.peek().get_token_kind() {
    //             TokenKind::Keyword(KeywordKind::Public) => {
    //                 self.advance();
    //                 QualifierKind::Public
    //             },
    //             TokenKind::Keyword(KeywordKind::Private) => {
    //                 self.advance();
    //                 QualifierKind::Private
    //             },
    //             _ => QualifierKind::Public
    //         };

    //         match self.peek().get_token_kind() {
    //             TokenKind::Keyword(KeywordKind::Let) => fields.push(self.parse_field_declaration(qualifier, true, span)?),
    //             TokenKind::Keyword(KeywordKind::Const) => fields.push(self.parse_field_declaration(qualifier, false, span)?),
    //             TokenKind::Keyword(KeywordKind::Fn) => methods.push(self.parse_method_declaration(qualifier, span, name.clone())?),
    //             _  => {
    //                 let position = self.previous().get_span().start_pos;
    //                 return Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected a method or function initialization, instead found {:?}.", self.peek().get_token_kind())));
    //             }
    //         }
    //     }

    //     self.advance();

    //     Ok(Node {
    //         kind: NodeKind::ClassDeclaration {
    //             name,
    //             parent,
    //             fields,
    //             methods
    //         },
    //         span: span.set_end_from_span(self.previous().get_span())
    //     })
    // }

    // fn parse_field_declaration(&mut self, qualifier: QualifierKind, instance: bool, span: Span) -> Result<Node, ParserError> {
    //     let variable_declaration = self.parse_variable_declaration(instance)?;

    //     let (name, type_annotation, initializer) = match variable_declaration.kind {
    //         NodeKind::VariableDeclaration { name, type_annotation, initializer, .. } 
    //             => (name, type_annotation, initializer),
    //         _ => unreachable!()
    //     };

    //     Ok(Node {
    //         kind: NodeKind::ClassField { 
    //             qualifier, 
    //             name, 
    //             type_annotation, 
    //             initializer,
    //             instance
    //         },
    //         span: span.set_end_from_span(self.previous().get_span())
    //     })
    // }

    // fn parse_method_declaration(&mut self, qualifier: QualifierKind, span: Span, class_name: String) -> Result<Node, ParserError> {
    //     self.advance();

    //     let name = self.consume(TokenKind::Identifier)?.get_value().to_string();

    //     let mut parameters = vec![];
    //     let mut instance = false;

    //     self.consume(TokenKind::OpenParenthesis)?;
        
    //     while self.peek().get_token_kind() != TokenKind::CloseParenthesis {
    //         let span = self.create_span_from_current_token();
    //         let token = self.advance();
        
    //         match token.get_token_kind() {
    //             TokenKind::Keyword(KeywordKind::This) => {
    //                 if parameters.is_empty() {
    //                     instance = true;
    //                     let type_annotation = Box::new(Node {
    //                         kind: NodeKind::Identifier(class_name.clone()),
    //                         span: span.set_end_from_span(self.previous().get_span())
    //                     });
    //                     parameters.push(Node {
    //                         kind: NodeKind::FunctionParameter {
    //                             name: "this".to_string(),
    //                             type_annotation,
    //                             initializer: None
    //                         },
    //                         span: span.set_end_from_span(self.previous().get_span())
    //                     });
    //                 } else {
    //                     let position = self.previous().get_span().start_pos;
    //                     return Err(ParserError::UnexpectedToken(position.line, position.column, "Expected an identifier, instead found `this`.".to_string()));
    //                 }
    //             },
    //             TokenKind::Identifier => {
    //                 let name = token.get_value().to_string();
    //                 self.consume(TokenKind::Colon)?;
    //                 let type_annotation = Box::new(self.parse_type()?);
    //                 let mut initializer = None;
        
    //                 if self.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
    //                     self.advance();
    //                     initializer = Some(Box::new(self.parse_expression()?));
    //                 }
        
    //                 parameters.push(Node {
    //                     kind: NodeKind::FunctionParameter {
    //                         name,
    //                         type_annotation,
    //                         initializer
    //                     },
    //                     span: span.set_end_from_span(self.previous().get_span())
    //                 });
    //             },
    //             _ => {
    //                 let position = self.previous().get_span().start_pos;
    //                 return Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected `this` or an identifier, instead found {:?}.", self.previous().get_token_kind())));
    //             }
    //         }
        
    //         if self.peek().get_token_kind() == TokenKind::Comma {
    //             self.consume(TokenKind::Comma)?;
    //         } else {
    //             break;
    //         }
    //     }

    //     self.consume(TokenKind::CloseParenthesis)?;

    //     let mut return_type = None;
    //     if self.peek().get_token_kind() == TokenKind::Colon {
    //         self.consume(TokenKind::Colon)?;
    //         return_type = Some(Box::new(self.parse_type()?));
    //     }

    //     let body = Box::new(self.parse_block()?);

    //     Ok(Node {
    //         kind: NodeKind::MethodDeclaration {
    //             qualifier,
    //             name,
    //             parameters,
    //             return_type,
    //             body,
    //             instance
    //         },
    //         span: span.set_end_from_span(self.previous().get_span())
    //     })
    // }
}