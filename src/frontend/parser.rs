use std::collections::HashMap;

use indexmap::IndexMap;

use crate::utils::{error::ParserError, kind::{KeywordKind, Operation, Position, QualifierKind, Span, Token, TokenKind, SYNC_TOKENS}};

use super::ast::{Node, NodeKind};

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
        self.parse_precedence(Operation::Assign.binding_power().0)
    }

    fn parse_precedence(&mut self, min_bp: u8) -> Result<Node, ParserError> {
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

            let token = self.peek().clone();
            let operator = match token.get_token_kind() {
                TokenKind::Operator(op) => op,
                _ => break,
            };

            let (left_bp, right_bp) = operator.binding_power();
            if left_bp < min_bp {
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

        while self.peek().get_token_kind() == TokenKind::OpenParenthesis {
            self.advance();
        
            let mut arguments = vec![];
            if self.peek().get_token_kind() != TokenKind::CloseParenthesis {
                loop {
                    arguments.push(self.parse_expression()?);
                    if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
                        break;
                    }
                    self.consume(TokenKind::Comma)?;
                }
            }
        
            self.consume(TokenKind::CloseParenthesis)?;
        
            lhs = Node {
                span: lhs.span.set_end_from_span(self.previous().get_span()),
                kind: NodeKind::FunctionCall {
                    function: Box::new(lhs),
                    arguments,
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
                let operand = Box::new(self.parse_precedence(Operation::Not.binding_power().0)?);

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
                let numeric_literal: String = token.get_value().to_string();

                let (is_integer, value): (bool, f64) = {
                    if numeric_literal.starts_with("0b") || numeric_literal.starts_with("0B") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 2)
                            .map_err(|_| panic!("The lexer made an error tokenizing token {:?}.", token))?;
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0o") || numeric_literal.starts_with("0O") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 8)
                            .map_err(|_| panic!("The lexer made an error tokenizing token {:?}.", token))?;
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0x") || numeric_literal.starts_with("0X") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 16)
                            .map_err(|_| panic!("The lexer made an error tokenizing token {:?}.", token))?;
                        (true, int_value as f64)
                    } else if numeric_literal.contains('.') || numeric_literal.contains('e') || numeric_literal.contains('E') {
                        let float_value = numeric_literal.parse::<f64>()
                            .map_err(|_| panic!("The lexer made an error tokenizing token {:?}.", token))?;
                        (false, float_value)
                    } else {
                        let int_value = numeric_literal.parse::<u64>()
                            .map_err(|_| panic!("The lexer made an error tokenizing token {:?}.", token))?;
                        (true, int_value as f64)
                    }
                };

                Ok(Node {
                    kind: if is_integer { NodeKind::IntegerLiteral(value as i64) } else { NodeKind::FloatLiteral(value) },
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
                    let mut fields = HashMap::new();

                    self.advance();
                    loop {
                        let name_token = self.consume(TokenKind::Identifier)?.clone();
                        let name = name_token.get_value().to_string();

                        let value = if self.peek().get_token_kind() == TokenKind::Colon {
                            self.consume(TokenKind::Colon)?;
                            self.parse_expression()?
                        } else {
                            Node {
                                kind: NodeKind::Identifier(name.clone()),
                                span: name_token.get_span()
                            }
                        };

                        fields.insert(name, value);
                        
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
            TokenKind::Keyword(KeywordKind::This) => {
                self.advance();
                Ok(Node {
                    kind: NodeKind::SelfValue,
                    span: span.set_end_from_span(self.previous().get_span())
                })
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
            KeywordKind::Impl => self.parse_impl_statement(),
            KeywordKind::Enum => self.parse_enum_statement(),
            KeywordKind::Trait => self.parse_trait_declaration(),
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
        let fn_signature_span = self.create_span_from_current_token();
        let fn_span = self.create_span_from_current_token();

        self.advance();

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();

        let parameters = self.parse_function_parameter_list()?;

        let mut return_type = None;
        if self.peek().get_token_kind() == TokenKind::Colon {
            self.consume(TokenKind::Colon)?;
            return_type = Some(Box::new(self.parse_type()?));
        }

        let signature = Box::new(Node {
            kind: NodeKind::FunctionSignature {
                name,
                parameters,
                return_type,
                instance: None
            },
            span: fn_signature_span.set_end_from_span(self.previous().get_span())
        });

        let body = Box::new(self.parse_block()?);

        Ok(Node {
            kind: NodeKind::FunctionDeclaration {
                signature,
                body
            },
            span: fn_span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_function_parameter_list(&mut self) -> Result<Vec<Node>, ParserError> {
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

    fn parse_associated_function_parameter_list(&mut self) -> Result<(Vec<Node>, bool), ParserError> {
        let mut parameters = vec![];
        let mut instance = false;

        self.consume(TokenKind::OpenParenthesis)?;
        
        while self.peek().get_token_kind() != TokenKind::CloseParenthesis {
            let span = self.create_span_from_current_token();
            let token = self.advance();
        
            match token.get_token_kind() {
                TokenKind::Keyword(KeywordKind::This) => {
                    if parameters.is_empty() {
                        instance = true;
                        let type_annotation = Box::new(Node {
                            kind: NodeKind::SelfType,
                            span: span.set_end_from_span(self.previous().get_span())
                        });
                        parameters.push(Node {
                            kind: NodeKind::FunctionParameter {
                                name: "this".to_string(),
                                type_annotation,
                                initializer: None
                            },
                            span: span.set_end_from_span(self.previous().get_span())
                        });
                    } else {
                        let position = self.previous().get_span().start_pos;
                        return Err(ParserError::UnexpectedToken(position.line, position.column, "Expected an identifier, instead found `this`.".to_string()));
                    }
                },
                TokenKind::Identifier => {
                    let name = token.get_value().to_string();
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
                },
                _ => {
                    let position = self.previous().get_span().start_pos;
                    return Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected `this` or an identifier, instead found {:?}.", self.previous().get_token_kind())));
                }
            }
        
            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }

        self.consume(TokenKind::CloseParenthesis)?;

        Ok((parameters, instance))
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

    fn parse_impl_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        self.advance();

        let (mut name, mut trait_name) = ("".to_string(), None);
        let temp_name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        if self.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::For) {
            self.advance();

            name = self.consume(TokenKind::Identifier)?.get_value().to_string();
            trait_name = Some(temp_name);
        } else {
            name = temp_name;
        }

        self.consume(TokenKind::OpenBrace)?;

        let mut associated_constants = vec![];
        let mut associated_functions = vec![];

        while self.peek().get_token_kind() != TokenKind::CloseBrace {
            let span = self.create_span_from_current_token();

            let qualifier = match self.peek().get_token_kind() {
                TokenKind::Keyword(KeywordKind::Public) => {
                    self.advance();
                    QualifierKind::Public
                },
                TokenKind::Keyword(KeywordKind::Private) => {
                    self.advance();
                    QualifierKind::Private
                },
                _ => QualifierKind::Public
            };

            match self.peek().get_token_kind() {
                TokenKind::Keyword(KeywordKind::Const) => associated_constants.push(self.parse_associated_constant_declaration(qualifier, span)?),
                TokenKind::Keyword(KeywordKind::Fn) => associated_functions.push(self.parse_associated_function_declaration(qualifier, span)?),
                _  => {
                    let position = self.previous().get_span().start_pos;
                    return Err(ParserError::UnexpectedToken(position.line, position.column, format!("Expected an associated function or an associated constant variable to be initialized, instead found {:?}.", self.peek().get_token_kind())));
                }
            }
        }

        self.advance();

        Ok(Node {
            kind: NodeKind::ImplDeclaration {
                name,
                trait_name,
                associated_constants,
                associated_functions
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_associated_constant_declaration(&mut self, qualifier: QualifierKind, span: Span) -> Result<Node, ParserError> {
        let variable_declaration = self.parse_variable_declaration(false)?;

        let (name, type_annotation, initializer) = match variable_declaration.kind {
            NodeKind::VariableDeclaration { name, type_annotation, initializer, .. } 
                => (name, type_annotation, initializer),
            _ => unreachable!()
        };

        let previous_span = self.previous().get_span();

        Ok(Node {
            kind: NodeKind::AssociatedConstant { 
                qualifier, 
                name, 
                type_annotation, 
                initializer: initializer.ok_or(ParserError::UninitializedConstant(previous_span.end_pos.line, previous_span.end_pos.column))?
            },
            span: span.set_end_from_span(previous_span)
        })
    }

    fn parse_associated_function_declaration(&mut self, qualifier: QualifierKind, span: Span) -> Result<Node, ParserError> {
        self.advance();

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        let (parameters, instance) = self.parse_associated_function_parameter_list()?;

        let mut return_type = None;
        if self.peek().get_token_kind() == TokenKind::Colon {
            self.consume(TokenKind::Colon)?;
            return_type = Some(Box::new(self.parse_type()?));
        }

        let body = Box::new(self.parse_block()?);

        Ok(Node {
            kind: NodeKind::AssociatedFunction {
                qualifier,
                name,
                parameters,
                return_type,
                body,
                instance
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_enum_statement(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        self.advance();

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        let mut variants = IndexMap::new();

        self.consume(TokenKind::OpenBrace)?;
        loop {
            let variant_name = self.consume(TokenKind::Identifier)?.get_value().to_string();
            if self.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                self.advance();
                variants.insert(variant_name, Some(self.parse_expression()?));
            } else {
                variants.insert(variant_name, None);
            }

            if self.peek().get_token_kind() == TokenKind::CloseBrace {
                break;
            } else {
                self.consume(TokenKind::Comma)?;
            }
        }
        self.consume(TokenKind::CloseBrace)?;

        Ok(Node {
            kind: NodeKind::EnumDeclaration { 
                name,
                variants
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_trait_declaration(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();
        self.advance();

        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        let mut signatures = vec![];

        self.consume(TokenKind::OpenBrace)?;
        while self.peek().get_token_kind() != TokenKind::CloseBrace {
            signatures.push(self.parse_function_signature()?);
            self.consume(TokenKind::Semicolon)?;
        }
        self.consume(TokenKind::CloseBrace)?;

        Ok(Node {
            kind: NodeKind::TraitDeclaration {
                name,
                signatures
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }

    fn parse_function_signature(&mut self) -> Result<Node, ParserError> {
        let span = self.create_span_from_current_token();

        self.consume(TokenKind::Keyword(KeywordKind::Fn))?;
        let name = self.consume(TokenKind::Identifier)?.get_value().to_string();
        let (parameters, instance) = self.parse_associated_function_parameter_list()?;
        let mut return_type = None;

        if self.peek().get_token_kind() == TokenKind::Colon {
            self.consume(TokenKind::Colon)?;
            return_type = Some(Box::new(self.parse_type()?));
        }

        Ok(Node {
            kind: NodeKind::FunctionSignature {
                name,
                parameters,
                return_type,
                instance: Some(instance)
            },
            span: span.set_end_from_span(self.previous().get_span())
        })
    }
}