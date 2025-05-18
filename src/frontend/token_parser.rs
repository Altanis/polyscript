use indexmap::IndexMap;

use crate::utils::{error::*, kind::*};

use super::ast::{AstNode, AstNodeKind};

pub struct Parser {
    lines: Vec<String>,
    tokens: Vec<Token>,
    current: usize,
    errors: Vec<Error>
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
    fn generate_error(&self, kind: ErrorKind, span: Span) -> Box<Error> {
        let span = span.set_end_from_span(self.previous().get_span());
        Error::from_one_error(kind, span, (self.lines[span.end_pos.line - 1].clone(), span.start_pos.line))
    }
    
    fn consume(&mut self, token_type: TokenKind) -> Result<&Token, Box<Error>> {
        let peeked = self.peek();

        if peeked.get_token_kind() == token_type {
            Ok(self.advance())
        } else {
            let span = self.peek().get_span();
            return Err(self.generate_error(
                ErrorKind::UnexpectedToken(
                    peeked.get_value().to_string(), format!("{}", peeked.get_token_kind()), format!("a token of type {}", token_type)
                ),
                span
            ))
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

    fn spanned_node<F>(&mut self, builder: F) -> Result<AstNode, Box<Error>>
    where
        F: FnOnce(&mut Self) -> Result<AstNodeKind, Box<Error>>,
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

        Ok(AstNode { kind, span: finished, ty: None, symbol: None })
    }
}

impl Parser {
    fn parse_expression(&mut self) -> Result<AstNode, Box<Error>> {
        self.parse_precedence(Operation::Assign.binding_power().0)
    }

    fn parse_precedence(&mut self, min_bp: u8) -> Result<AstNode, Box<Error>> {
        let mut lhs = self.parse_prefix()?;

        loop {
            match self.peek().get_token_kind() {
                TokenKind::Operator(operator) if operator.is_postfix() => {
                    lhs = AstNode {
                        span: lhs.span.set_end_from_span(self.peek().get_span()),
                        kind: AstNodeKind::UnaryOperation {
                            operator,
                            operand: Box::new(lhs),
                            prefix: false
                        },
                        ty: None,
                        symbol: None
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

            lhs = AstNode {
                span: lhs.span.set_end_from_span(rhs.span),
                kind: match token.get_token_kind() {
                    TokenKind::Operator(op) => {
                        if op.is_conditional() {
                            AstNodeKind::ConditionalOperation {
                                operator,
                                left: Box::new(lhs),
                                right: Box::new(rhs),
                            }
                        } else {
                            AstNodeKind::BinaryOperation {
                                operator,
                                left: Box::new(lhs),
                                right: Box::new(rhs),
                            }
                        }
                    },
                    _ => unreachable!()
                },
                ty: None,
                symbol: None
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
        
            lhs = AstNode {
                span: lhs.span.set_end_from_span(self.previous().get_span()),
                kind: AstNodeKind::FunctionCall {
                    function: Box::new(lhs),
                    arguments,
                },
                ty: None,
                symbol: None
            };
        }

        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<AstNode, Box<Error>> {
        let token = self.peek();
        let span = self.create_span_from_current_token();

        match token.get_token_kind() {
            TokenKind::Operator(operator) => {
                if !operator.is_unary() {
                    return Err(self.generate_error(
                        ErrorKind::UnexpectedToken(
                            token.get_value().to_string(),
                            format!("{}", token.get_token_kind()),
                            "a unary operator".to_string()
                        ),
                        span
                    ));
                }

                let _ = self.advance();
                let mut operator = match operator {
                    Operation::Mul => Operation::Dereference,
                    Operation::BitwiseAnd => Operation::ImmutableAddressOf,
                    _ => operator
                };

                if operator == Operation::ImmutableAddressOf &&
                    self.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Mut) 
                {
                    self.advance();
                    operator = Operation::MutableAddressOf;
                }

                let operand = Box::new(self.parse_precedence(Operation::Not.binding_power().0)?);

                Ok(AstNode {
                    span: span.set_end_from_span(operand.span),
                    kind: AstNodeKind::UnaryOperation { 
                        operator,
                        operand,
                        prefix: true
                    },
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::NumberLiteral(_) => {
                let token = self.advance();
                let numeric_literal: String = token.get_value().to_string();

                let (is_integer, value): (bool, f64) = {
                    if numeric_literal.starts_with("0b") || numeric_literal.starts_with("0B") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 2)
                            .unwrap_or_else(|_| panic!("The lexer made an error tokenizing token {:?}.", token));
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0o") || numeric_literal.starts_with("0O") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 8)
                            .unwrap_or_else(|_| panic!("The lexer made an error tokenizing token {:?}.", token));
                        (true, int_value as f64)
                    } else if numeric_literal.starts_with("0x") || numeric_literal.starts_with("0X") {
                        let without_prefix = &numeric_literal[2..];
                        let int_value = u64::from_str_radix(without_prefix, 16)
                            .unwrap_or_else(|_| panic!("The lexer made an error tokenizing token {:?}.", token));
                        (true, int_value as f64)
                    } else if numeric_literal.contains('.') || numeric_literal.contains('e') || numeric_literal.contains('E') {
                        let float_value = numeric_literal.parse::<f64>()
                            .unwrap_or_else(|_| panic!("The lexer made an error tokenizing token {:?}.", token));
                        (false, float_value)
                    } else {
                        let int_value = numeric_literal.parse::<u64>()
                            .unwrap_or_else(|_| panic!("The lexer made an error tokenizing token {:?}.", token));
                        (true, int_value as f64)
                    }
                };

                Ok(AstNode {
                    kind: if is_integer { AstNodeKind::IntegerLiteral(value as i64) } else { AstNodeKind::FloatLiteral(value) },
                    span: token.get_span(),
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::BooleanLiteral => {
                let token = self.advance();
                let value = token.get_value().parse::<bool>().unwrap();

                Ok(AstNode {
                    kind: AstNodeKind::BooleanLiteral(value),
                    span: token.get_span(),
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::StringLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].to_string();

                Ok(AstNode {
                    kind: AstNodeKind::StringLiteral(value),
                    span: token.get_span(),
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::CharLiteral => {
                let token = self.advance();

                let raw_value = token.get_value();
                let value = raw_value[1..raw_value.len() - 1].chars().next().unwrap();

                Ok(AstNode {
                    kind: AstNodeKind::CharLiteral(value),
                    span: token.get_span(),
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::Identifier => {
                let token = self.advance();
                let name = token.get_value().to_string();
                let span = token.get_span();

                if self.peek().get_token_kind() == TokenKind::OpenBrace {
                    let mut fields = IndexMap::new();

                    self.advance();
                    loop {
                        let name_token = self.consume(TokenKind::Identifier)?.clone();
                        let name = name_token.get_value().to_string();

                        let value = if self.peek().get_token_kind() == TokenKind::Colon {
                            self.consume(TokenKind::Colon)?;
                            self.parse_expression()?
                        } else {
                            AstNode {
                                kind: AstNodeKind::Identifier(name.clone()),
                                span: name_token.get_span(),
                                ty: None,
                                symbol: None
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
                        kind: AstNodeKind::StructLiteral {
                            name,
                            fields
                        },
                        span: span.set_end_from_span(self.previous().get_span()),
                        ty: None,
                        symbol: None
                    })
                } else {
                    Ok(AstNode {
                        kind: AstNodeKind::Identifier(name),
                        span,
                        ty: None,
                        symbol: None
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
                Ok(AstNode {
                    kind: AstNodeKind::SelfValue,
                    span: span.set_end_from_span(self.previous().get_span()),
                    ty: None,
                    symbol: None
                })
            },
            TokenKind::Keyword(KeywordKind::Fn) => {
                self.parse_function_expression()
            },
            _ => {
                return Err(self.generate_error(
                    ErrorKind::UnexpectedToken(
                        token.get_value().to_string(),
                        format!("{}", token.get_token_kind()),
                        "a unary operator, a literal, an identifier, open parentheses, or a function expression".to_string()
                    ),
                    span
                ));
            }
        }
    }

    fn parse_expression_statement(&mut self) -> Result<AstNode, Box<Error>> {
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
            errors: vec![]
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
                }
            },
            ty: None,
            symbol: None
        }
    }

    fn parse_statement(&mut self) -> Result<AstNode, Box<Error>> {
        let token = self.peek();
        match token.get_token_kind() {
            TokenKind::Keyword(kind) => self.parse_keyword(kind),
            TokenKind::OpenBrace => self.parse_block(),
            _ => self.parse_expression_statement()
        }
    }

    fn parse_keyword(&mut self, kind: KeywordKind) -> Result<AstNode, Box<Error>> {
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
            KeywordKind::Type => self.parse_type_declaration(),
            _ => self.parse_expression_statement()
        }
    }

    fn parse_block(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::OpenBrace)?;
            
            let mut statements = vec![];
        
            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                let stmt = parser.parse_statement()?;
                statements.push(stmt);
            }
        
            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::Block(statements))
        })
    }

    fn parse_variable_declaration(&mut self, mutable: bool) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();

            let var_name = parser.consume(TokenKind::Identifier)?.get_value().to_string();

            let mut type_annotation = None;
            if parser.match_token(TokenKind::Colon) {
                type_annotation = Some(Box::new(parser.parse_type()?));
            }

            let mut initializer = None;
            if parser.match_token(TokenKind::Operator(Operation::Assign)) {
                initializer = Some(Box::new(parser.parse_expression()?));
            }

            if !mutable && initializer.is_none() {
                return Err(parser.generate_error(ErrorKind::UninitializedConstant, parser.previous().get_span()));
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

    fn parse_type(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            let type_reference = parser.advance().clone();
            match type_reference.get_token_kind() {
                TokenKind::Identifier 
                    | TokenKind::Keyword(KeywordKind::Int)
                    | TokenKind::Keyword(KeywordKind::Float)
                    | TokenKind::Keyword(KeywordKind::String)
                    | TokenKind::Keyword(KeywordKind::Bool)
                => {
                    let generic_types = parser.parse_generic_types_list()?;

                    Ok(AstNodeKind::TypeReference {
                        type_name: type_reference.get_value().to_string(),
                        generic_types
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
                        return_type = Some(Box::new(parser.parse_type()?));
                    }


                    Ok(AstNodeKind::FunctionPointer {
                        params,
                        return_type
                    })
                },
                _ => {
                    let span = type_reference.get_span();
                    return Err(parser.generate_error(
                        ErrorKind::UnexpectedToken(type_reference.get_value().to_string(), format!("{}", type_reference.get_token_kind()), "a type reference".to_string()),
                        span
                    ));
                }
            }
        })
    }

    fn parse_function_declaration(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            let signature = Box::new(parser.parse_function_signature(false, false, true)?);
            let body = Box::new(parser.parse_block()?);

            Ok(AstNodeKind::FunctionDeclaration {
                signature,
                body
            })
        })
    }

    fn parse_function_expression(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            let signature = Box::new(parser.parse_function_signature(true, false, false)?);
            let body = Box::new(parser.parse_block()?);

            Ok(AstNodeKind::FunctionExpression {
                signature,
                body
            })
        })
    }

    fn parse_parameter(&mut self, allow_this: bool, is_first: bool) -> Result<(AstNode, bool), Box<Error>> {
        let mut is_this_param = false;

        let node = self.spanned_node(|parser| {
            let token = parser.advance().clone();
            match token.get_token_kind() {
                TokenKind::Operator(Operation::BitwiseAnd) => {
                    let operator = if parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Mut) {
                        parser.advance();
                        Operation::MutableAddressOf
                    } else {
                        Operation::ImmutableAddressOf
                    };

                    parser.consume(TokenKind::Keyword(KeywordKind::This))?;

                    if allow_this && is_first {
                        is_this_param = true;

                        let type_annotation = Box::new(parser.spanned_node(|_| {
                            Ok(AstNodeKind::SelfType(Some(operator)))
                        })?);

                        Ok(AstNodeKind::FunctionParameter {
                            name: "this".to_string(),
                            type_annotation,
                            initializer: None,
                        })
                    } else {
                        let span = parser.previous().get_span();
                        return Err(parser.generate_error(
                            ErrorKind::UnexpectedToken("this".to_string(), "<this>".to_string(), "an identifier".to_string()),
                            span
                        ));
                    }
                },
                TokenKind::Keyword(KeywordKind::This) => {
                    if allow_this && is_first {
                        is_this_param = true;

                        let type_annotation = Box::new(parser.spanned_node(|_| {
                            Ok(AstNodeKind::SelfType(None))
                        })?);

                        Ok(AstNodeKind::FunctionParameter {
                            name: "this".to_string(),
                            type_annotation,
                            initializer: None,
                        })
                    } else {
                        let span = parser.previous().get_span();
                        return Err(parser.generate_error(
                            ErrorKind::UnexpectedToken("this".to_string(), "<this>".to_string(), "an identifier".to_string()),
                            span
                        ));
                    }
                },
                TokenKind::Identifier => {
                    let name = token.get_value().to_string();
                    parser.consume(TokenKind::Colon)?;
                    let type_annotation = Box::new(parser.parse_type()?);
                    let mut initializer = None;

                    if parser.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                        parser.advance();
                        initializer = Some(Box::new(parser.parse_expression()?));
                    }

                    Ok(AstNodeKind::FunctionParameter {
                        name,
                        type_annotation,
                        initializer,
                    })
                },
                _ => {
                    let span = token.get_span();
                    return Err(parser.generate_error(
                        ErrorKind::UnexpectedToken(token.get_value().to_string(), format!("{}", token.get_token_kind()), "<this> or an identifier".to_string()),
                        span
                    ));
                }
            }
        })?;

        Ok((node, is_this_param))
    }

    fn parse_function_parameter_list(&mut self) -> Result<Vec<AstNode>, Box<Error>> {
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

    fn parse_associated_function_parameter_list(&mut self) -> Result<(Vec<AstNode>, bool), Box<Error>> {
        let mut parameters = vec![];
        let mut instance = false;

        self.consume(TokenKind::OpenParenthesis)?;

        let mut first = true;
        while self.peek().get_token_kind() != TokenKind::CloseParenthesis {
            let (param, is_instance) = self.parse_parameter(true, first)?;
            if is_instance {
                instance = true;
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
        Ok((parameters, instance))
    }
    
    fn parse_generic_parameter_list(&mut self) -> Result<Vec<AstNode>, Box<Error>> {
        let mut parameters = vec![];

        if self.peek().get_token_kind() != TokenKind::OpenBracket {
            return Ok(parameters);
        }
        
        self.consume(TokenKind::OpenBracket)?;
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

                Ok(AstNodeKind::GenericParameter {
                    name,
                    constraints
                })
            })?;

            parameters.push(node);

            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }
        self.consume(TokenKind::CloseBracket)?;

        Ok(parameters)
    }

    fn parse_generic_types_list(&mut self) -> Result<Vec<AstNode>, Box<Error>> {
        let mut types = vec![];

        if self.peek().get_token_kind() != TokenKind::OpenBracket {
            return Ok(types);
        }
        
        self.consume(TokenKind::OpenBracket)?;
        loop {
            let node = self.parse_type()?;
            types.push(node);

            if self.peek().get_token_kind() == TokenKind::Comma {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }
        self.consume(TokenKind::CloseBracket)?;

        Ok(types)
    }

    fn parse_selection_statements(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let condition = Box::new(parser.parse_expression()?);
            let then_branch = Box::new(parser.parse_block()?);
            let mut else_if_branches = vec![];

            let mut else_branch = None;

            while parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::Else) {
                parser.advance();

                if parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::If) {
                    parser.advance();
                    let condition = Box::new(parser.parse_expression()?);
                    let then_branch = Box::new(parser.parse_block()?);

                    else_if_branches.push((condition, then_branch));
                } else {
                    else_branch = Some(Box::new(parser.parse_block()?));
                }
            }

            Ok(AstNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch
            })
        })
    }

    fn parse_while_loop(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();

            let condition = Box::new(parser.parse_expression()?);
            let body = Box::new(parser.parse_block()?);

            Ok(AstNodeKind::WhileLoop {
                body,
                condition
            })
        })
    }

    fn parse_for_loop(&mut self) -> Result<AstNode, Box<Error>> {
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
                Some(Box::new(init))
            };
        
            let condition = if parser.peek().get_token_kind() == TokenKind::Semicolon {
                parser.consume(TokenKind::Semicolon)?;
                None
            } else {
                let cond = parser.parse_expression()?;
                parser.consume(TokenKind::Semicolon)?;
                Some(Box::new(cond))
            };
        
            let increment = if parser.peek().get_token_kind() == TokenKind::CloseParenthesis {
                None
            } else {
                Some(Box::new(parser.parse_expression()?))
            };
        
            parser.consume(TokenKind::CloseParenthesis)?;
            let body = Box::new(parser.parse_block()?);
        
            Ok(AstNodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            })
        })
    }

    fn parse_return_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();

            let expression = if parser.peek().get_token_kind() != TokenKind::Semicolon {
                Some(Box::new(parser.parse_expression_statement()?))
            } else {
                parser.advance();
                None
            };

            Ok(AstNodeKind::Return(expression))
        })
    }

    fn parse_throw_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();

            let expression = Box::new(parser.parse_expression_statement()?);

            Ok(AstNodeKind::Throw(expression))
        })
    }

    fn parse_continue_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::Continue)
        })
    }

    fn parse_break_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::Break)
        })
    }

    fn parse_struct_declaration(&mut self) -> Result<AstNode, Box<Error>> {
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
                fields
            })
        })
    }

    fn parse_struct_field(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            let qualifier_token = parser.advance().clone();
            let qualifier = match qualifier_token.get_token_kind() {
                TokenKind::Keyword(KeywordKind::Public) => QualifierKind::Public,
                TokenKind::Keyword(KeywordKind::Private) => QualifierKind::Private,
                _ => {
                    let span = qualifier_token.get_span();
                    return Err(parser.generate_error(
                        ErrorKind::UnexpectedToken(qualifier_token.get_value().to_string(), format!("{}", qualifier_token.get_token_kind()), "a type reference".to_string()),
                        span
                    ));
                }
            };

            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            parser.consume(TokenKind::Colon)?;
            let type_annotation = Box::new(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::StructField {
                qualifier,
                name,
                type_annotation
            })
        })
    }

    fn parse_impl_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let generic_parameters = parser.parse_generic_parameter_list()?;

            let (type_node, trait_name) = {
                let first = parser.advance().clone();

                if parser.peek().get_token_kind() == TokenKind::Keyword(KeywordKind::For) {
                    parser.advance();
                    let type_node = parser.parse_type()?;
                    let trait_name = Some(first.get_value().to_string());
                    (type_node, trait_name)
                } else {
                    parser.back();
                    (parser.parse_type()?, None)
                }
            };

            parser.consume(TokenKind::OpenBrace)?;

            let mut associated_constants = vec![];
            let mut associated_functions = vec![];

            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                let qualifier = match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Public) => {
                        parser.advance();
                        QualifierKind::Public
                    },
                    TokenKind::Keyword(KeywordKind::Private) => {
                        parser.advance();
                        QualifierKind::Private
                    },
                    _ => QualifierKind::Public
                };

                match parser.peek().get_token_kind() {
                    TokenKind::Keyword(KeywordKind::Const) => associated_constants.push(parser.parse_associated_constant_declaration(qualifier)?),
                    TokenKind::Keyword(KeywordKind::Fn) => associated_functions.push(parser.parse_associated_function_declaration(qualifier)?),
                    kind => {
                        let span = parser.previous().get_span();
                        return Err(parser.generate_error(
                            ErrorKind::UnexpectedToken(parser.peek().get_value().to_string(), format!("{}", kind), "an associated function or constant".to_string()),
                            span
                        ));
                    }
                }
            }

            parser.advance();

            Ok(AstNodeKind::ImplDeclaration {
                generic_parameters,
                type_reference: Box::new(type_node),
                trait_name,
                associated_constants,
                associated_functions
            })
        })
    }

    fn parse_associated_constant_declaration(&mut self, qualifier: QualifierKind) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            let variable_declaration = parser.parse_variable_declaration(false)?;

            let (name, type_annotation, initializer) = match variable_declaration.kind {
                AstNodeKind::VariableDeclaration { name, type_annotation, initializer, .. } 
                    => (name, type_annotation, initializer),
                _ => unreachable!()
            };

            let initializer = initializer.ok_or(parser.generate_error(ErrorKind::UninitializedConstant, parser.previous().get_span()))?;

            Ok(AstNodeKind::AssociatedConstant { 
                qualifier, 
                name, 
                type_annotation, 
                initializer
            })
        })
    }

    fn parse_associated_function_declaration(&mut self, qualifier: QualifierKind) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let generic_parameters = parser.parse_generic_parameter_list()?;
            let (parameters, instance) = parser.parse_associated_function_parameter_list()?;

            let mut return_type = None;
            if parser.peek().get_token_kind() == TokenKind::Colon {
                parser.consume(TokenKind::Colon)?;
                return_type = Some(Box::new(parser.parse_type()?));
            }

            let signature = Box::new(AstNode {
                kind: AstNodeKind::FunctionSignature {
                    name,
                    generic_parameters,
                    parameters,
                    return_type,
                    instance: Some(instance)
                },
                span: Span::default(),
                ty: None,
                symbol: None
            });

            let body = Box::new(parser.parse_block()?);

            Ok(AstNodeKind::AssociatedFunction {
                qualifier,
                signature,
                body
            })
        })
    }

    fn parse_enum_statement(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let mut variants = IndexMap::new();

            parser.consume(TokenKind::OpenBrace)?;
            loop {
                let variant_name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
                if parser.peek().get_token_kind() == TokenKind::Operator(Operation::Assign) {
                    parser.advance();
                    variants.insert(variant_name, Some(parser.parse_expression()?));
                } else {
                    variants.insert(variant_name, None);
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

    fn parse_trait_declaration(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let mut signatures = vec![];

            parser.consume(TokenKind::OpenBrace)?;
            while parser.peek().get_token_kind() != TokenKind::CloseBrace {
                signatures.push(parser.parse_function_signature(false, true, true)?);
                parser.consume(TokenKind::Semicolon)?;
            }
            parser.consume(TokenKind::CloseBrace)?;

            Ok(AstNodeKind::TraitDeclaration { name, signatures })
        })
    }

    fn parse_function_signature(&mut self, anonymous: bool, associated_fn: bool, allowed_generic_parameters: bool) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.consume(TokenKind::Keyword(KeywordKind::Fn))?;

            let name = if !anonymous {
                parser.consume(TokenKind::Identifier)?.get_value().to_string()
            } else {
                String::new()
            };

            let generic_parameters = if allowed_generic_parameters {
                parser.parse_generic_parameter_list()?
            } else {
                vec![]
            };

            let (parameters, instance) = if associated_fn {
                let (params, has_instance) = parser.parse_associated_function_parameter_list()?;
                (params, Some(has_instance))
            } else {
                (parser.parse_function_parameter_list()?, None)
            };

            let mut return_type = None;
            if parser.peek().get_token_kind() == TokenKind::Colon {
                parser.consume(TokenKind::Colon)?;
                return_type = Some(Box::new(parser.parse_type()?));
            }

            Ok(AstNodeKind::FunctionSignature {
                name,
                generic_parameters,
                parameters,
                return_type,
                instance
            })
        })
    }

    fn parse_type_declaration(&mut self) -> Result<AstNode, Box<Error>> {
        self.spanned_node(|parser| {
            parser.advance();
            let name = parser.consume(TokenKind::Identifier)?.get_value().to_string();
            let generic_parameters = parser.parse_generic_parameter_list()?;
            parser.consume(TokenKind::Operator(Operation::Assign))?;
            let value = Box::new(parser.parse_type()?);
            parser.consume(TokenKind::Semicolon)?;

            Ok(AstNodeKind::TypeDeclaration {
                name,
                generic_parameters,
                value
            })
        })
    }
}