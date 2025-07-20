use indexmap::IndexMap;

use crate::{
    boxed,
    frontend::ast::BoxedAstNode,
    utils::{error::*, kind::*},
};

use super::ast::{AstNode, AstNodeKind};

pub struct Parser {
    lines: Vec<String>,
    tokens: Vec<Token>,
    current: usize,
    errors: Vec<Error>,
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

    fn back(&mut self) {
        if self.current > 0 {
            self.current -= 1;
        }
    }

    fn match_token(&mut self, token_type: TokenKind) -> bool {
        if self.peek().get_token_kind() == token_type {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Generates an Error struct based on the position of the parser.
    fn generate_error(&self, kind: ErrorKind, span: Span) -> BoxedError {
        let span = span.set_end_from_span(self.peek().get_span());
        Error::from_one_error(
            kind,
            span,
            (self.lines[span.end_pos.line - 1].clone(), span.start_pos.line),
        )
    }

    fn consume(&mut self, token_type: TokenKind) -> Result<&Token, BoxedError> {
        let peeked = self.peek();

        if peeked.get_token_kind() == token_type {
            Ok(self.advance())
        } else {
            let span = self.previous().get_span();
            return Err(self.generate_error(
                ErrorKind::UnexpectedToken(
                    peeked.get_value().to_string(),
                    format!("{}", peeked.get_token_kind()),
                    format!("a token of type {}", token_type),
                ),
                span,
            ));
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
            end_pos: Position::default(),
        }
    }

    fn spanned_node<F>(&mut self, builder: F) -> Result<AstNode, BoxedError>
    where
        F: FnOnce(&mut Self) -> Result<AstNodeKind, BoxedError>,
    {
        let start_span = self.peek().get_span();
        let initial = Span {
            start: start_span.start,
            start_pos: start_span.start_pos,
            end: 0,
            end_pos: Position::default(),
        };

        let kind = builder(self)?;
        let finished = initial.set_end_from_span(self.previous().get_span());

        Ok(AstNode {
            kind,
            span: finished,
            type_id: None,
            value_id: None,
            scope_id: None,
        })
    }
}

impl Parser {
    fn parse_expression(&mut self) -> Result<AstNode, BoxedError> {
        self.parse_binding_power(Operation::Assign.binding_power().0)
    }

    fn parse_binding_power(&mut self, min_bp: u8) -> Result<AstNode, BoxedError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            let operator = match self.peek().get_token_kind() {
                TokenKind::Operator(op) => op,
                TokenKind::OpenParenthesis => Operation::FunctionCall,
                _ => break,
            };

            let (left_bp, right_bp) = operator.binding_power();

            if left_bp < min_bp {
                break;
            }

            self.advance();

            if operator == Operation::As {
                let target_type = self.parse_type()?;
                
                lhs = AstNode {
                    span: lhs.span.set_end_from_span(target_type.span),
                    kind: AstNodeKind::TypeCast {
                        expr: boxed!(lhs),
                        target_type: boxed!(target_type),
                    },
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                };
            } else if operator == Operation::FunctionCall {
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

                lhs = AstNode {
                    span: lhs.span.set_end_from_span(self.previous().get_span()),
                    kind: AstNodeKind::FunctionCall {
                        function: boxed!(lhs),
                        arguments,
                    },
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                };
            } else {
                let rhs = self.parse_binding_power(right_bp)?;

                lhs = AstNode {
                    span: lhs.span.set_end_from_span(rhs.span),
                    kind: if operator.is_conditional() {
                        AstNodeKind::ConditionalOperation {
                            operator,
                            left: boxed!(lhs),
                            right: boxed!(rhs),
                        }
                    } else if operator == Operation::FieldAccess {
                        AstNodeKind::FieldAccess {
                            left: boxed!(lhs),
                            right: boxed!(rhs),
                        }
                    } else {
                        AstNodeKind::BinaryOperation {
                            operator,
                            left: boxed!(lhs),
                            right: boxed!(rhs),
                        }
                    },
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                };
            }
        }

        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<AstNode, BoxedError> {
        let token = self.peek();
        let span = self.create_span_from_current_token();

        match token.get_token_kind() {
            TokenKind::Operator(Operation::LessThan) => {
                return self.spanned_node(|parser| {
                    parser.consume(TokenKind::Operator(Operation::LessThan))?;

                    let ty = boxed!(parser.parse_type()?);
                    let tr = if parser.match_token(TokenKind::Operator(Operation::As)) {
                        Some(boxed!(parser.parse_type()?))
                    } else {
                        None
                    };
                    parser.consume(TokenKind::Operator(Operation::GreaterThan))?;

                    Ok(AstNodeKind::PathQualifier { ty, tr })
                })
            },
            TokenKind::Operator(operator) => {
                if !operator.is_unary() {
                    return Err(self.generate_error(
                        ErrorKind::UnexpectedToken(
                            token.get_value().to_string(),
                            format!("{}", token.get_token_kind()),
                            "a unary operator".to_string(),
                        ),
                        span,
                    ));
                }

                let _ = self.advance();
                let mut operator = match operator {
                    Operation::Mul => Operation::Dereference,
                    Operation::BitwiseAnd => Operation::ImmutableAddressOf,
                    _ => operator,
                };

                if operator == Operation::ImmutableAddressOf
                    && self.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Mut)
                {
                    self.advance();
                    operator = Operation::MutableAddressOf;
                }

                let operand = boxed!(self.parse_binding_power(Operation::Not.binding_power().0)?);

                Ok(AstNode {
                    span: span.set_end_from_span(operand.span),
                    kind: AstNodeKind::UnaryOperation { operator, operand },
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::NumberLiteral(_) => {
                let token = self.advance();
                let numeric_literal: String = token.get_value().to_string();

                let (is_integer, value): (bool, f64) = {
                    if numeric_literal.starts_with("0b") || numeric_literal.starts_with("0B") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 2).unwrap_or_else(|_| {
                            panic!("The lexer made an error tokenizing token {:?}.", token)
                        });
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0o") || numeric_literal.starts_with("0O") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 8).unwrap_or_else(|_| {
                            panic!("The lexer made an error tokenizing token {:?}.", token)
                        });
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0x") || numeric_literal.starts_with("0X") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 16).unwrap_or_else(|_| {
                            panic!("The lexer made an error tokenizing token {:?}.", token)
                        });
                        (true, int_value as f64)
                    } else if numeric_literal.contains('.')
                        || numeric_literal.contains('e')
                        || numeric_literal.contains('E')
                    {
                        let float_value = numeric_literal.parse::<f64>().unwrap_or_else(|_| {
                            panic!("The lexer made an error tokenizing token {:?}.", token)
                        });
                        (false, float_value)
                    } else {
                        let int_value = numeric_literal.parse::<u64>().unwrap_or_else(|_| {
                            panic!("The lexer made an error tokenizing token {:?}.", token)
                        });
                        (true, int_value as f64)
                    }
                };

                Ok(AstNode {
                    kind: if is_integer {
                        AstNodeKind::IntegerLiteral(value as i64)
                    } else {
                        AstNodeKind::FloatLiteral(value)
                    },
                    span: token.get_span(),
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::BooleanLiteral => {
                let token = self.advance();
                let value = token.get_value().parse::<bool>().unwrap();

                Ok(AstNode {
                    kind: AstNodeKind::BooleanLiteral(value),
                    span: token.get_span(),
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::StringLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].to_string();

                Ok(AstNode {
                    kind: AstNodeKind::StringLiteral(value),
                    span: token.get_span(),
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::CharLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].chars().next().unwrap();

                Ok(AstNode {
                    kind: AstNodeKind::CharLiteral(value),
                    span: token.get_span(),
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::Identifier => {
                let token = self.advance();
                let name = token.get_value().to_string();
                let span = token.get_span();

                if self.peek().get_token_kind() == TokenKind::OpenBrace {
                    let mut fields = IndexMap::new();

                    self.advance();
                    while self.peek().get_token_kind() != TokenKind::CloseBrace {
                        let name_token = self.consume(TokenKind::Identifier)?.clone();
                        let name = name_token.get_value().to_string();

                        let value = if self.peek().get_token_kind() == TokenKind::Colon {
                            self.consume(TokenKind::Colon)?;
                            self.parse_expression()?
                        } else {
                            AstNode {
                                kind: AstNodeKind::Identifier(name.clone()),
                                span: name_token.get_span(),
                                type_id: None,
                                value_id: None,
                                scope_id: None,
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

                    Ok(AstNode {
                        kind: AstNodeKind::StructLiteral { name, fields },
                        span: span.set_end_from_span(self.previous().get_span()),
                        type_id: None,
                        value_id: None,
                        scope_id: None,
                    })
                } else {
                    Ok(AstNode {
                        kind: AstNodeKind::Identifier(name),
                        span,
                        type_id: None,
                        value_id: None,
                        scope_id: None,
                    })
                }
            }
            TokenKind::OpenParenthesis => {
                self.advance();
                let expr = self.parse_expression()?;
                self.consume(TokenKind::CloseParenthesis)?;
                Ok(expr)
            },
            TokenKind::OpenBrace => self.parse_block(),
            TokenKind::Keyword(KeywordKind::This) => {
                self.advance();
                Ok(AstNode {
                    kind: AstNodeKind::SelfValue,
                    span: span.set_end_from_span(self.previous().get_span()),
                    type_id: None,
                    value_id: None,
                    scope_id: None,
                })
            }
            TokenKind::Keyword(KeywordKind::Fn) => self.parse_function_expression(),
            TokenKind::Keyword(KeywordKind::If) => self.parse_if_expression(),
            _ => {
                return Err(self.generate_error(
                    ErrorKind::UnexpectedToken(
                        token.get_value().to_string(),
                        format!("{}", token.get_token_kind()),
                        "a unary operator, a literal, an identifier, open parentheses, a function expression, or an if expression".to_string()
                    ),
                    span
                ));
            }
        }
    }

    fn parse_expression_statement(&mut self) -> Result<AstNode, BoxedError> {
        let node = self.parse_expression()?;
        self.consume(TokenKind::Semicolon)?;
        Ok(node)
    }
}

impl Parser {
    pub fn new(lined_source: Vec<String>, tokens: Vec<Token>) -> Parser {
        Parser {
            lines: lined_source,
            tokens,
            current: 0,
            errors: vec![],
        }
    }

    pub fn parse(&mut self) -> Result<AstNode, Vec<Error>> {
        let program = self.parse_program();
        if self.errors.is_empty() {
            Ok(program)
        } else {
            Err(self.errors.clone())
        }
    }

    fn parse_program(&mut self) -> AstNode {
        let mut statements = vec![];

        while !self.is_at_end() {
            match self.parse_statement() {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.errors.push(*err);
                    self.synchronize();
                }
            }
        }

        AstNode {
            kind: AstNodeKind::Program(statements),
            span: Span {
                start: 0,
                end: self.tokens.last().unwrap().get_span().end,
                start_pos: Position::default(),
                end_pos: Position {
                    line: self.tokens.last().unwrap().get_span().end_pos.line,
                    column: self.tokens.last().unwrap().get_span().end_pos.column,
                },
            },
            type_id: None,
            value_id: None,
            scope_id: None,
        }
    }

    fn parse_statement(&mut self) -> Result<AstNode, BoxedError> {
        let token = self.peek();
        match token.get_token_kind() {
            TokenKind::Keyword(kind) => self.parse_keyword(kind),
            TokenKind::OpenBrace => self.parse_block(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_keyword(&mut self, kind: KeywordKind) -> Result<AstNode, BoxedError> {
        match kind {
            KeywordKind::Let => self.parse_variable_declaration(true),
            KeywordKind::Const => self.parse_variable_declaration(false),
            KeywordKind::Fn => self.parse_function_declaration(),
            KeywordKind::While => self.parse_while_loop(),
            KeywordKind::For => self.parse_for_loop(),
            KeywordKind::Struct => self.parse_struct_declaration(),
            KeywordKind::Return => self.parse_return_statement(),
            KeywordKind::Break => self.parse_break_statement(),
            KeywordKind::Continue => self.parse_continue_statement(),
            KeywordKind::Impl => self.parse_impl_statement(),
            KeywordKind::Enum => self.parse_enum_statement(),
            KeywordKind::Trait => self.parse_trait_declaration(),
            KeywordKind::Type => self.parse_type_declaration(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_block(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::OpenBrace)?;

            let mut statements = vec![];
            while !parser.is_at_end() && parser.peek().get_token_kind() != TokenKind::CloseBrace {
                let checkpoint = parser.current;
                
                if let Ok(expr) = parser.parse_expression() {
                    if parser.peek().get_token_kind() == TokenKind::CloseBrace {
                        statements.push(expr);
                        break; 
                    }
                }
                
                parser.current = checkpoint;
                statements.push(parser.parse_statement()?);
            }

            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::Block(statements))
        })
    }

    fn parse_variable_declaration(&mut self, mutable: bool) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();

            let var_name = parser.consume(TokenKind::Identifier)?.get_value().to_string();

            let mut type_annotation = None;
            if parser.match_token(TokenKind::Colon) {
                type_annotation = Some(boxed!(parser.parse_type()?));
            }

            let mut initializer = None;
            if parser.match_token(TokenKind::Operator(Operation::Assign)) {
                initializer = Some(boxed!(parser.parse_expression()?));
            }

            if !mutable && initializer.is_none() {
                return Err(
                    parser.generate_error(ErrorKind::UninitializedConstant, parser.previous().get_span())
                );
            }

            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::VariableDeclaration {
                mutable,
                name: var_name,
                type_annotation,
                initializer,
            })
        })
    }

    fn parse_type(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let mut reference_kind = ReferenceKind::Value;

            if parser.peek().get_token_kind() == TokenKind::Operator(Operation::BitwiseAnd) {
                parser.advance();

                if parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Mut) {
                    parser.advance();
                    reference_kind = ReferenceKind::MutableReference;
                } else {
                    reference_kind = ReferenceKind::Reference;
                }
            }

            let type_reference = parser.advance().clone();

            match type_reference.get_token_kind() {
                TokenKind::Identifier => {
                    if parser.peek().get_token_kind() == TokenKind::Operator(Operation::FieldAccess) {
                        parser.advance();
                        let next = parser.consume(TokenKind::Identifier)?;

                        Ok(AstNodeKind::FieldAccess {
                            left: boxed!(AstNode {
                                kind: AstNodeKind::Identifier(type_reference.get_value().to_string()),
                                span: type_reference.get_span(),
                                value_id: None,
                                scope_id: None,
                                type_id: None
                            }),
                            right: boxed!(AstNode {
                                kind: AstNodeKind::Identifier(next.get_value().to_string()),
                                span: next.get_span(),
                                value_id: None,
                                scope_id: None,
                                type_id: None
                            }),
                        })
                    } else {
                        let generic_types = parser.parse_generic_types_list()?;

                        Ok(AstNodeKind::TypeReference {
                            type_name: type_reference.get_value().to_string(),
                            generic_types,
                            reference_kind,
                        })
                    }
                },

                TokenKind::Keyword(KeywordKind::Int)
                | TokenKind::Keyword(KeywordKind::Float)
                | TokenKind::Keyword(KeywordKind::String)
                | TokenKind::Keyword(KeywordKind::Bool)
                | TokenKind::Keyword(KeywordKind::Char) => {
                    let generic_types = parser.parse_generic_types_list()?;

                    Ok(AstNodeKind::TypeReference {
                        type_name: type_reference.get_value().to_string(),
                        generic_types,
                        reference_kind,
                    })
                },
                TokenKind::Keyword(KeywordKind::Fn) => {
                    let mut params = vec![];

                    parser.consume(TokenKind::OpenParenthesis)?;
                    loop {
                        params.push(parser.parse_type()?);
                        if parser.peek().get_token_kind() == TokenKind::Comma {
                            parser.advance();
                        } else {
                            break;
                        }
                    }
                    parser.consume(TokenKind::CloseParenthesis)?;

                    let mut return_type = None;

                    if parser.peek().get_token_kind() == TokenKind::Colon {
                        parser.advance();
                        return_type = Some(boxed!(parser.parse_type()?));
                    }

                    Ok(AstNodeKind::FunctionPointer { params, return_type })
                },
                TokenKind::Operator(Operation::LessThan) => {
                    let ty = boxed!(parser.parse_type()?);

                    let tr = if parser.match_token(TokenKind::Operator(Operation::As)) {
                        Some(boxed!(parser.parse_type()?))
                    } else {
                        None
                    };

                    parser.consume(TokenKind::Operator(Operation::GreaterThan))?;

                    let kind = AstNodeKind::PathQualifier { ty, tr };

                    if parser.peek().get_token_kind() == TokenKind::Operator(Operation::FieldAccess) {
                        parser.advance();
                        let next = parser.consume(TokenKind::Identifier)?;

                        Ok(AstNodeKind::FieldAccess {
                            left: boxed!(AstNode {
                                kind,
                                span: type_reference.get_span(),
                                value_id: None,
                                scope_id: None,
                                type_id: None
                            }),
                            right: boxed!(AstNode {
                                kind: AstNodeKind::Identifier(next.get_value().to_string()),
                                span: next.get_span(),
                                value_id: None,
                                scope_id: None,
                                type_id: None
                            }),
                        })
                    } else {
                        Ok(kind)
                    }
                },
                _ => {
                    let span = type_reference.get_span();
                    Err(parser.generate_error(
                        ErrorKind::UnexpectedToken(
                            type_reference.get_value().to_string(),
                            format!("{}", type_reference.get_token_kind()),
                            "a type reference".to_string(),
                        ),
                        span,
                    ))
                }
            }
        })
    }

    fn parse_function_signature(
        &mut self,
        is_expression: bool,
        is_associated: bool,
        allow_generics: bool,
    ) -> Result<
        (
            String,
            Vec<AstNode>,
            Vec<AstNode>,
            Option<BoxedAstNode>,
            Option<ReferenceKind>,
        ),
        BoxedError,
    > {
        self.consume(TokenKind::Keyword(KeywordKind::Fn))?;

        let name = if !is_expression {
            self.consume(TokenKind::Identifier)?.get_value().to_string()
        } else {
            String::new()
        };

        let generic_parameters = if allow_generics {
            self.parse_generic_parameter_list()?
        } else {
            vec![]
        };

        let (parameters, instance) = if is_associated {
            self.parse_associated_function_parameter_list()?
        } else {
            (self.parse_function_parameter_list()?, None)
        };

        let mut return_type = None;
        if self.match_token(TokenKind::Colon) {
            return_type = Some(boxed!(self.parse_type()?));
        }

        Ok((name, generic_parameters, parameters, return_type, instance))
    }

    fn parse_function_declaration(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let (name, generic_parameters, parameters, return_type, instance) =
                parser.parse_function_signature(false, false, true)?;
            let body = Some(boxed!(parser.parse_block()?));

            Ok(AstNodeKind::Function {
                qualifier: None,
                name,
                generic_parameters,
                parameters,
                return_type,
                instance,
                body,
            })
        })
    }

    fn parse_function_expression(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let (name, generic_parameters, parameters, return_type, instance) =
                parser.parse_function_signature(true, false, false)?;
            let body = Some(boxed!(parser.parse_block()?));

            Ok(AstNodeKind::Function {
                qualifier: None,
                name,
                generic_parameters,
                parameters,
                return_type,
                instance,
                body,
            })
        })
    }

    fn parse_parameter(
        &mut self,
        allow_this: bool,
        is_first: bool,
    ) -> Result<(AstNode, Option<ReferenceKind>), BoxedError> {
        let mut self_kind: Option<ReferenceKind> = None;

        let node = self.spanned_node(|parser| {
            if allow_this && is_first {
                let current_token_kind = parser.peek().get_token_kind();
                if current_token_kind == TokenKind::Operator(Operation::BitwiseAnd) {
                    let next_token_is_mut = parser.tokens.get(parser.current + 1).map_or(false, |t| {
                        t.get_token_kind() == TokenKind::Keyword(KeywordKind::Mut)
                    });
                    let next_token_is_this = parser.tokens.get(parser.current + 1).map_or(false, |t| {
                        t.get_token_kind() == TokenKind::Keyword(KeywordKind::This)
                    });
                    let third_token_is_this = next_token_is_mut
                        && parser.tokens.get(parser.current + 2).map_or(false, |t| {
                            t.get_token_kind() == TokenKind::Keyword(KeywordKind::This)
                        });

                    if next_token_is_this || third_token_is_this {
                        parser.advance();

                        let (_, kind) = if parser.match_token(TokenKind::Keyword(KeywordKind::Mut)) {
                            (Operation::MutableAddressOf, ReferenceKind::MutableReference)
                        } else {
                            (Operation::ImmutableAddressOf, ReferenceKind::Reference)
                        };

                        parser.consume(TokenKind::Keyword(KeywordKind::This))?;
                        self_kind = Some(kind);

                        let type_annotation =
                            boxed!(parser.spanned_node(|_| Ok(AstNodeKind::SelfType(kind)))?);
                        return Ok(AstNodeKind::FunctionParameter {
                            name: "this".to_string(),
                            type_annotation,
                            initializer: None,
                            mutable: false,
                        });
                    }
                } else if current_token_kind == TokenKind::Keyword(KeywordKind::This) {
                    parser.advance();
                    self_kind = Some(ReferenceKind::Value);

                    let type_annotation =
                        boxed!(parser.spanned_node(|_| Ok(AstNodeKind::SelfType(ReferenceKind::Value)))?);
                    return Ok(AstNodeKind::FunctionParameter {
                        name: "this".to_string(),
                        type_annotation,
                        initializer: None,
                        mutable: false,
                    });
                }
            }

            let mutable = parser.match_token(TokenKind::Keyword(KeywordKind::Mut));
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Colon)?;
            let type_annotation = boxed!(parser.parse_type()?);
            let mut initializer = None;

            if parser.match_token(TokenKind::Operator(Operation::Assign)) {
                initializer = Some(boxed!(parser.parse_expression()?));
            }

            Ok(AstNodeKind::FunctionParameter {
                name,
                type_annotation,
                initializer,
                mutable,
            })
        })?;

        Ok((node, self_kind))
    }

    fn parse_function_parameter_list(&mut self) -> Result<Vec<AstNode>, BoxedError> {
        let mut parameters = vec![];

        self.consume(TokenKind::OpenParenthesis)?;
        if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
            self.consume(TokenKind::CloseParenthesis)?;
            return Ok(parameters);
        }

        let mut first = true;
        loop {
            let (param, _) = self.parse_parameter(false, first)?;
            parameters.push(param);
            first = false;

            if self.peek().get_token_kind() == TokenKind::CloseParenthesis {
                break;
            } else {
                self.consume(TokenKind::Comma)?;
            }
        }

        self.consume(TokenKind::CloseParenthesis)?;
        Ok(parameters)
    }

    fn parse_associated_function_parameter_list(
        &mut self,
    ) -> Result<(Vec<AstNode>, Option<ReferenceKind>), BoxedError> {
        let mut parameters = vec![];
        let mut instance_kind: Option<ReferenceKind> = None;

        self.consume(TokenKind::OpenParenthesis)?;

        let mut first = true;
        while self.peek().get_token_kind() != TokenKind::CloseParenthesis {
            let (param, self_kind) = self.parse_parameter(true, first)?;
            if self_kind.is_some() {
                instance_kind = self_kind;
            }
            parameters.push(param);
            first = false;

            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }

        self.consume(TokenKind::CloseParenthesis)?;
        Ok((parameters, instance_kind))
    }

    fn parse_generic_parameter_list(&mut self) -> Result<Vec<AstNode>, BoxedError> {
        let mut parameters = vec![];

        if self.peek().get_token_kind() != TokenKind::Operator(Operation::LessThan) {
            return Ok(parameters);
        }

        self.consume(TokenKind::Operator(Operation::LessThan))?;
        loop {
            let node = self.spanned_node(|parser| {
                let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
                let mut constraints = vec![];

                if parser.peek().get_token_kind() == TokenKind::Colon {
                    parser.advance();

                    loop {
                        constraints.push(parser.consume(TokenKind::Identifier)?.get_value().to_string());
                        if parser.peek().get_token_kind() != TokenKind::Operator(Operation::Plus) {
                            break;
                        }

                        parser.advance();
                    }
                }

                Ok(AstNodeKind::GenericParameter { name, constraints })
            })?;

            parameters.push(node);

            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }

        self.consume(TokenKind::Operator(Operation::GreaterThan))?;

        Ok(parameters)
    }

    fn parse_generic_types_list(&mut self) -> Result<Vec<AstNode>, BoxedError> {
        let mut types = vec![];

        if self.peek().get_token_kind() != TokenKind::Operator(Operation::LessThan) {
            return Ok(types);
        }

        self.consume(TokenKind::Operator(Operation::LessThan))?;
        loop {
            let node = self.parse_type()?;
            types.push(node);

            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }

        self.consume(TokenKind::Operator(Operation::GreaterThan))?;

        Ok(types)
    }

    fn parse_if_expression(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::Keyword(KeywordKind::If))?;
            let condition = boxed!(parser.parse_expression()?);
            let then_branch = boxed!(parser.parse_block()?);
            let mut else_if_branches = vec![];
            let mut else_branch = None;

            while parser.match_token(TokenKind::Keyword(KeywordKind::Else)) {
                if parser.match_token(TokenKind::Keyword(KeywordKind::If)) {
                    let else_if_condition = boxed!(parser.parse_expression()?);
                    let else_if_branch = boxed!(parser.parse_block()?);
                    else_if_branches.push((else_if_condition, else_if_branch));
                } else {
                    else_branch = Some(boxed!(parser.parse_block()?));
                    break;
                }
            }

            Ok(AstNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            })
        })
    }

    fn parse_while_loop(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();

            let condition = boxed!(parser.parse_expression()?);
            let body = boxed!(parser.parse_block()?);

            Ok(AstNodeKind::WhileLoop { body, condition })
        })
    }

    fn parse_for_loop(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            parser.consume(TokenKind::OpenParenthesis)?;

            let initializer = if parser.peek().get_token_kind() == TokenKind::Semicolon {
                parser.consume(TokenKind::Semicolon)?;
                None
            } else {
                let init = match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Let) => parser.parse_variable_declaration(true),
                    TokenKind::Keyword(KeywordKind::Const) => parser.parse_variable_declaration(false),
                    _ => parser.parse_expression_statement(),
                }?;
                Some(boxed!(init))
            };

            let condition = if parser.peek().get_token_kind() == TokenKind::Semicolon {
                parser.consume(TokenKind::Semicolon)?;
                None
            } else {
                let cond = parser.parse_expression()?;
                parser.consume(TokenKind::Semicolon)?;
                Some(boxed!(cond))
            };

            let increment = if parser.peek().get_token_kind() == TokenKind::CloseParenthesis {
                None
            } else {
                Some(boxed!(parser.parse_expression()?))
            };

            parser.consume(TokenKind::CloseParenthesis)?;
            let body = boxed!(parser.parse_block()?);

            Ok(AstNodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            })
        })
    }

    fn parse_return_statement(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();

            let expression = if parser.peek().get_token_kind() != TokenKind::Semicolon {
                let expr = boxed!(parser.parse_expression()?);
                parser.consume(TokenKind::Semicolon)?;
                Some(expr)
            } else {
                parser.advance();
                None
            };

            Ok(AstNodeKind::Return(expression))
        })
    }

    fn parse_continue_statement(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::Continue)
        })
    }

    fn parse_break_statement(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::Break)
        })
    }

    fn parse_struct_declaration(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();

            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let generic_parameters = parser.parse_generic_parameter_list()?;
            let mut fields = vec![];

            parser.consume(TokenKind::OpenBrace)?;
            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                fields.push(parser.parse_struct_field()?);
            }
            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::StructDeclaration {
                name,
                generic_parameters,
                fields,
            })
        })
    }

    fn parse_struct_field(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let qualifier_token = parser.advance().clone();
            let qualifier = match qualifier_token.get_token_kind() {
                TokenKind::Keyword(KeywordKind::Public) => QualifierKind::Public,
                TokenKind::Keyword(KeywordKind::Private) => QualifierKind::Private,
                _ => {
                    parser.back();
                    QualifierKind::Public
                }
            };

            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Colon)?;
            let type_annotation = boxed!(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::StructField {
                qualifier,
                name,
                type_annotation,
            })
        })
    }

    fn parse_impl_statement(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            let generic_parameters = parser.parse_generic_parameter_list()?;

            let (type_node, trait_node) = {
                let first = parser.parse_type()?;
                if parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::For) {
                    parser.advance();
                    let second = parser.parse_type()?;

                    (boxed!(second), Some(boxed!(first)))
                } else {
                    (boxed!(first), None)
                }
            };

            parser.consume(TokenKind::OpenBrace)?;

            let mut associated_constants = vec![];
            let mut associated_functions = vec![];
            let mut associated_types = vec![];

            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                let qualifier = match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Public) => {
                        parser.advance();
                        QualifierKind::Public
                    }
                    TokenKind::Keyword(KeywordKind::Private) => {
                        parser.advance();
                        QualifierKind::Private
                    }
                    _ => QualifierKind::Public,
                };

                match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Const) => {
                        associated_constants.push(parser.parse_associated_constant_declaration(qualifier)?)
                    }
                    TokenKind::Keyword(KeywordKind::Fn) => {
                        associated_functions.push(parser.parse_associated_function(qualifier)?)
                    }
                    TokenKind::Keyword(KeywordKind::Type) => {
                        associated_types.push(parser.parse_associated_type_declaration(qualifier)?)
                    }
                    kind => {
                        let span = parser.previous().get_span();
                        return Err(parser.generate_error(
                            ErrorKind::UnexpectedToken(
                                parser.peek().get_value().to_string(),
                                format!("{}", kind),
                                "an associated function, type, or constant".to_string(),
                            ),
                            span,
                        ));
                    }
                }
            }

            parser.advance();

            Ok(AstNodeKind::ImplDeclaration {
                generic_parameters,
                type_reference: type_node,
                trait_node,
                associated_constants,
                associated_functions,
                associated_types,
            })
        })
    }

    fn parse_associated_constant_declaration(
        &mut self,
        qualifier: QualifierKind,
    ) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let variable_declaration = parser.parse_variable_declaration(false)?;

            let (name, type_annotation, initializer) = match variable_declaration.kind {
                AstNodeKind::VariableDeclaration {
                    name,
                    type_annotation,
                    initializer,
                    ..
                } => (name, type_annotation, initializer),
                _ => unreachable!(),
            };

            let initializer = initializer.ok_or(
                parser.generate_error(ErrorKind::UninitializedConstant, parser.previous().get_span()),
            )?;

            Ok(AstNodeKind::AssociatedConstant {
                qualifier,
                name,
                type_annotation,
                initializer,
            })
        })
    }

    fn parse_associated_function(&mut self, qualifier: QualifierKind) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let (name, generic_parameters, parameters, return_type, instance) =
                parser.parse_function_signature(false, true, true)?;
            let body = Some(boxed!(parser.parse_block()?));

            Ok(AstNodeKind::Function {
                qualifier: Some(qualifier),
                name,
                generic_parameters,
                parameters,
                return_type,
                instance,
                body,
            })
        })
    }

    fn parse_associated_type_declaration(&mut self, qualifier: QualifierKind) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Operator(Operation::Assign))?;
            let value = boxed!(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::AssociatedType {
                name,
                value,
                qualifier,
            })
        })
    }

    fn parse_enum_statement(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let mut variants = IndexMap::new();

            parser.consume(TokenKind::OpenBrace)?;
            loop {
                let variant = parser.parse_enum_variant()?;
                let AstNodeKind::EnumVariant(name) = &variant.kind else {
                    unreachable!();
                };

                if parser.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                    parser.advance();
                    variants.insert(name.clone(), (variant, Some(parser.parse_expression()?)));
                } else {
                    variants.insert(name.clone(), (variant, None));
                }

                if parser.peek().get_token_kind() == TokenKind::CloseBrace {
                    break;
                } else {
                    parser.consume(TokenKind::Comma)?;
                }
            }
            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::EnumDeclaration { name, variants })
        })
    }

    fn parse_enum_variant(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let variant_name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            Ok(AstNodeKind::EnumVariant(variant_name))
        })
    }

    fn parse_trait_declaration(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();

            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let generic_parameters = parser.parse_generic_parameter_list()?;

            let mut signatures = vec![];
            let mut constants = vec![];
            let mut types = vec![];

            parser.consume(TokenKind::OpenBrace)?;
            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Const) => constants.push(parser.parse_trait_constant()?),
                    TokenKind::Keyword(KeywordKind::Fn) => {
                        signatures.push(parser.parse_trait_method_signature()?)
                    }
                    TokenKind::Keyword(KeywordKind::Type) => types.push(parser.parse_trait_type()?),
                    kind => {
                        let span = parser.previous().get_span();
                        return Err(parser.generate_error(
                            ErrorKind::UnexpectedToken(
                                parser.peek().get_value().to_string(),
                                format!("{}", kind),
                                "a function signature, type, or constant".to_string(),
                            ),
                            span,
                        ));
                    }
                }
            }

            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::TraitDeclaration {
                name,
                generic_parameters,
                signatures,
                constants,
                types,
            })
        })
    }

    fn parse_trait_constant(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::Keyword(KeywordKind::Const))?;
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Colon)?;
            let type_annotation = boxed!(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::TraitConstant {
                name,
                type_annotation,
            })
        })
    }

    fn parse_trait_method_signature(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            let (name, generic_parameters, parameters, return_type, instance) =
                parser.parse_function_signature(false, true, true)?;
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::Function {
                qualifier: None,
                name,
                generic_parameters,
                parameters,
                return_type,
                instance,
                body: None,
            })
        })
    }

    fn parse_trait_type(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::Keyword(KeywordKind::Type))?;
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::TraitType(name))
        })
    }

    fn parse_type_declaration(&mut self) -> Result<AstNode, BoxedError> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let generic_parameters = parser.parse_generic_parameter_list()?;
            parser.consume(TokenKind::Operator(Operation::Assign))?;
            let value = boxed!(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::TypeDeclaration {
                name,
                generic_parameters,
                value,
            })
        })
    }
}
