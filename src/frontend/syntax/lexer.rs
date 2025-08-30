use crate::utils::{error::*, kind::*};

trait CharClassifier {
    fn is_operation(self) -> bool;
    fn valid_alphabetic_hex(self) -> bool;
}

impl CharClassifier for char {
    fn is_operation(self) -> bool {
        matches!(
            self,
            NOT_TOKEN
                | BITWISE_NEGATE_TOKEN
                | ADD_TOKEN
                | SUB_TOKEN
                | MUL_TOKEN
                | DIV_TOKEN
                | MOD_TOKEN
                | BITWISE_AND_TOKEN
                | BITWISE_OR_TOKEN
                | BITWISE_XOR_TOKEN
                | ASSIGNMENT_TOKEN
                | GREATER_THAN_TOKEN
                | LESS_THAN_TOKEN
                | FIELD_ACCESS_TOKEN
        )
    }

    fn valid_alphabetic_hex(self) -> bool {
        matches!(self.to_ascii_lowercase(), 'a' | 'b' | 'c' | 'd' | 'e' | 'f')
    }
}

pub struct Lexer {
    /// The source program, in lines.
    lines: Vec<String>,
    /// The source program, as characters.
    source: Vec<char>,
    /// The line the lexer is reading.
    line: usize,
    /// The index in the line the lexer is reading.
    column: usize,
    /// The index in the source the lexer is reading.
    index: usize,
    /// The tokens collected from the source.
    tokens: Vec<Token>,
}

impl Lexer {
    /// Goes to the next line.
    fn next_line(&mut self) {
        self.line += 1;
        self.column = 1;
    }

    /// Goes to the index, or next line if '\n' is encountered.
    fn next_index(&mut self) {
        if self.source[self.index] == '\n' {
            self.next_line();
        } else {
            self.column += 1;
        }

        self.index += 1;
    }

    /// Generates an Error struct based on the position of the lexer.
    fn generate_error(&self, kind: ErrorKind, span: Option<Span>) -> BoxedError {
        let span = if let Some(span) = span {
            span.set_end_from_values(self.index, self.line, self.column)
        } else {
            Span {
                start: self.index,
                end: self.index,
                start_pos: Position {
                    line: self.line,
                    column: self.column,
                },
                end_pos: Position {
                    line: self.line,
                    column: self.column,
                },
            }
        };

        Error::from_one_error(kind, span, (self.lines[span.end_pos.line - 1].clone(), self.line))
    }

    /// Peeks forward `n` characters.
    fn peek_forward(&self, n: usize) -> Result<char, BoxedError> {
        self.source
            .get(self.index + n)
            .ok_or(self.generate_error(ErrorKind::UnexpectedEOF, None))
            .copied()
    }

    /// Peeks at the next character.
    fn peek(&self) -> Result<char, BoxedError> {
        self.peek_forward(1)
    }

    /// Consumes the next character.
    fn consume(&mut self) -> Result<char, BoxedError> {
        self.next_index();
        self.source
            .get(self.index)
            .ok_or(self.generate_error(ErrorKind::UnexpectedEOF, None))
            .copied()
    }

    fn parse_escape_char(&mut self) -> Result<char, BoxedError> {
        match self.consume()? {
            'n' => Ok('\n'),
            't' => Ok('\t'),
            'r' => Ok('\r'),
            '0' => Ok('\0'),
            '\\' => Ok('\\'),
            '\'' => Ok('\''),
            '\"' => Ok('\"'),
            'b' => Ok('\x08'),
            'f' => Ok('\x0C'),
            'v' => Ok('\x0B'),

            'x' => {
                let mut hex = String::new();
                for _ in 0..2 {
                    match self.consume()? {
                        c if c.is_ascii_hexdigit() => hex.push(c),
                        c => {
                            return Err(self.generate_error(
                                ErrorKind::InvalidEscapeSequence(format!(
                                    "\\x{} (invalid char '{}')",
                                    hex, c
                                )),
                                None,
                            ));
                        }
                    }
                }
                let value = u8::from_str_radix(&hex, 16).unwrap();
                Ok(value as char)
            }

            'u' => {
                if self.consume()? != '{' {
                    return Err(self.generate_error(
                        ErrorKind::InvalidEscapeSequence("\\u (does not have opening brace)".to_string()),
                        None,
                    ));
                }

                let mut hex = String::new();
                while let Ok(c) = self.consume() {
                    if c == '}' {
                        break;
                    }

                    if !c.is_ascii_hexdigit() {
                        return Err(self.generate_error(
                            ErrorKind::InvalidEscapeSequence(format!(
                                "\\u{{{}}} (invalid char '{}')",
                                hex + &c.to_string(),
                                c
                            )),
                            None,
                        ));
                    }

                    hex.push(c);

                    if hex.len() > 6 {
                        return Err(self.generate_error(
                            ErrorKind::InvalidEscapeSequence(format!(
                                "\\u{{{}}} (too long of an escape sequence)",
                                hex
                            )),
                            None,
                        ));
                    }
                }

                if hex.is_empty() {
                    return Err(
                        self.generate_error(ErrorKind::InvalidEscapeSequence("\\u{}".to_string()), None)
                    );
                }

                let value = u32::from_str_radix(&hex, 16).unwrap();
                match char::from_u32(value) {
                    Some(ch) => Ok(ch),
                    None => Err(self.generate_error(
                        ErrorKind::InvalidEscapeSequence(format!("\\u{{{}}} (invalid Unicode scalar)", hex)),
                        None,
                    )),
                }
            }

            other => Err(self.generate_error(ErrorKind::InvalidEscapeSequence(format!("\\{}", other)), None)),
        }
    }
}

impl Lexer {
    /// Parses an operation.
    fn parse_operator(&mut self) -> Result<Token, BoxedError> {
        let mut operator = self.source[self.index].to_string();
        let span = Span {
            start: self.index,
            end: 0,
            start_pos: Position {
                line: self.line,
                column: self.column,
            },
            end_pos: Position::default(),
        };

        match operator.chars().next().unwrap() {
            NOT_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::NotEqual)
                    }
                    _ => TokenKind::Operator(Operation::Not),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            BITWISE_NEGATE_TOKEN => Ok(Token::new(
                operator,
                TokenKind::Operator(Operation::BitwiseNegate),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            ADD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::PlusEq)
                    }
                    _ => TokenKind::Operator(Operation::Plus),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            SUB_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::MinusEq)
                    }
                    _ => TokenKind::Operator(Operation::Minus),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            MUL_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::MulEq)
                    }
                    Ok(c) if c == MUL_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::Exp)
                    }
                    _ => TokenKind::Operator(Operation::Mul),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            DIV_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::DivEq)
                    }
                    _ => TokenKind::Operator(Operation::Div),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            MOD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::ModEq)
                    }
                    _ => TokenKind::Operator(Operation::Mod),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            BITWISE_AND_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_AND_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::And)
                    }
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::BitwiseAndEq)
                    }
                    _ => TokenKind::Operator(Operation::BitwiseAnd),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            BITWISE_OR_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_OR_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::Or)
                    }
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::BitwiseOrEq)
                    }
                    _ => TokenKind::Operator(Operation::BitwiseOr),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            BITWISE_XOR_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::BitwiseXorEq)
                    }
                    _ => TokenKind::Operator(Operation::BitwiseXor),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            ASSIGNMENT_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Operator(Operation::Equivalence)
                    }
                    _ => TokenKind::Operator(Operation::Assign),
                };
                Ok(Token::new(
                    operator,
                    token_type,
                    span.set_end_from_values(self.index, self.line, self.column),
                ))
            }
            GREATER_THAN_TOKEN => match self.peek() {
                Ok(c) if c == ASSIGNMENT_TOKEN => {
                    operator.push(self.consume()?);
                    Ok(Token::new(
                        operator,
                        TokenKind::Operator(Operation::Geq),
                        span.set_end_from_values(self.index, self.line, self.column),
                    ))
                }
                Ok(c) if c == GREATER_THAN_TOKEN => {
                    operator.push(self.consume()?);
                    if let Ok(c2) = self.peek()
                        && c2 == ASSIGNMENT_TOKEN
                    {
                        operator.push(self.consume()?);
                        return Ok(Token::new(
                            operator,
                            TokenKind::Operator(Operation::RightBitShiftEq),
                            span.set_end_from_values(self.index, self.line, self.column),
                        ));
                    }
                    
                    Ok(Token::new(
                        operator,
                        TokenKind::Operator(Operation::RightBitShift),
                        span.set_end_from_values(self.index, self.line, self.column),
                    ))
                }
                _ => Ok(Token::new(
                    operator,
                    TokenKind::Operator(Operation::GreaterThan),
                    span.set_end_from_values(self.index, self.line, self.column),
                )),
            },
            LESS_THAN_TOKEN => match self.peek() {
                Ok(c) if c == ASSIGNMENT_TOKEN => {
                    operator.push(self.consume()?);
                    Ok(Token::new(
                        operator,
                        TokenKind::Operator(Operation::Leq),
                        span.set_end_from_values(self.index, self.line, self.column),
                    ))
                }
                Ok(c) if c == LESS_THAN_TOKEN => {
                    operator.push(self.consume()?);
                    if let Ok(c2) = self.peek()
                        && c2 == ASSIGNMENT_TOKEN
                    {
                        operator.push(self.consume()?);
                        return Ok(Token::new(
                            operator,
                            TokenKind::Operator(Operation::LeftBitShiftEq),
                            span.set_end_from_values(self.index, self.line, self.column),
                        ));
                    }

                    Ok(Token::new(
                        operator,
                        TokenKind::Operator(Operation::LeftBitShift),
                        span.set_end_from_values(self.index, self.line, self.column),
                    ))
                }
                _ => Ok(Token::new(
                    operator,
                    TokenKind::Operator(Operation::LessThan),
                    span.set_end_from_values(self.index, self.line, self.column),
                )),
            },
            FIELD_ACCESS_TOKEN => Ok(Token::new(
                operator,
                TokenKind::Operator(Operation::FieldAccess),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            _ => Err(self.generate_error(ErrorKind::UnrecognizedSymbol(operator), Some(span))),
        }
    }

    /// Parses a word.
    fn parse_word(&mut self) -> Result<Token, BoxedError> {
        let mut word = self.source[self.index].to_string();
        let span = Span {
            start: self.index,
            end: 0,
            start_pos: Position {
                line: self.line,
                column: self.column,
            },
            end_pos: Position::default(),
        };

        while let Ok(char) = self.peek()
            && (char.is_alphanumeric() || char == '_')
        {
            self.next_index();
            word.push(self.source[self.index]);
        }

        match word.as_str() {
            INT_TYPE => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Int),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            FLOAT_TYPE => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Float),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            BOOL_TYPE => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Bool),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            STATIC_STRING_TYPE => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::String),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CHAR_TYPE => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Char),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            LET_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Let),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CONST_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Const),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            STRUCT_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Struct),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            ENUM_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Enum),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            TRUE_KEYWORD | FALSE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::BooleanLiteral,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            FN_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Fn),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            FOR_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::For),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            WHILE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::While),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            RETURN_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Return),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            BREAK_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Break),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CONTINUE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Continue),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            IF_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::If),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            ELSE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Else),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            SELF_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::SelfKw),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            PUBLIC_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Public),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            PRIVATE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Private),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            IMPL_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Impl),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            TRAIT_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Trait),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            TYPE_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Type),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            MUT_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Mut),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            AS_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Operator(Operation::As),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            HEAP_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Heap),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            IMPORT_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Import),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            FROM_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::From),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            EXPORT_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Export),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            SIZEOF_KEYWORD => Ok(Token::new(
                word,
                TokenKind::Keyword(KeywordKind::Sizeof),
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            _ => Ok(Token::new(
                word,
                TokenKind::Identifier,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
        }
    }

    /// Parses a number.
    fn parse_number(&mut self) -> Result<Token, BoxedError> {
        let mut number_str = String::new();
        let mut has_decimal_point = false;
        let mut has_exponent = false;

        let first_char = self.source[self.index];
        number_str.push(first_char);
        let span = Span {
            start: self.index,
            end: 0,
            start_pos: Position {
                line: self.line,
                column: self.column,
            },
            end_pos: Position::default(),
        };

        if first_char == '0'
            && let Ok(next_char) = self.peek()
            && let Some(base) = match next_char.to_ascii_lowercase()
        {
            'b' => Some(2),
            'o' => Some(8),
            'x' => Some(16),
            _ => None,
        } {
            number_str.push(self.consume()?);
            let mut has_digits = false;

            while let Ok(c) = self.peek() {
                if c.is_digit(base) {
                    number_str.push(self.consume()?);
                    has_digits = true;
                } else {
                    break;
                }
            }

            if !has_digits {
                let invalid_char = self.peek().unwrap_or('\0');
                return Err(self
                    .generate_error(ErrorKind::InvalidDigit(invalid_char.to_string()), Some(span)));
            }

            let number_type = match base {
                2 => NumberKind::Binary,
                8 => NumberKind::Octal,
                16 => NumberKind::Hex,
                _ => unreachable!(),
            };

            return Ok(Token::new(
                number_str,
                TokenKind::NumberLiteral(number_type),
                span.set_end_from_values(self.index, self.line, self.column),
            ));
        }
        
        while let Ok(next_char) = self.peek() {
            if next_char.is_ascii_digit() {
                number_str.push(self.consume()?);
            } else if next_char == '.' && !has_decimal_point && !has_exponent {
                self.consume()?;

                if let Ok(peek_after_dot) = self.peek() {
                    if peek_after_dot.is_ascii_digit() {
                        has_decimal_point = true;
                        number_str.push('.');
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else if (next_char == 'e' || next_char == 'E') && !has_exponent {
                has_exponent = true;
                number_str.push(self.consume()?);

                if let Ok(sign) = self.peek()
                    && (sign == '+' || sign == '-')
                {
                    number_str.push(self.consume()?);
                }

                let mut exponent_digit_found = false;
                while let Ok(digit) = self.peek() {
                    if digit.is_ascii_digit() {
                        exponent_digit_found = true;
                        number_str.push(self.consume()?);
                    } else {
                        break;
                    }
                }

                if !exponent_digit_found {
                    let invalid_char = self.peek().unwrap_or('\0');
                    return Err(
                        self.generate_error(ErrorKind::InvalidDigit(invalid_char.to_string()), Some(span))
                    );
                }
            } else {
                break;
            }
        }

        let number_type = if has_decimal_point || has_exponent {
            NumberKind::Float
        } else {
            NumberKind::Decimal
        };

        Ok(Token::new(
            number_str,
            TokenKind::NumberLiteral(number_type),
            span.set_end_from_values(self.index, self.line, self.column),
        ))
    }

    fn parse_symbol(&mut self) -> Result<Token, BoxedError> {
        let symbol = self.source[self.index];
        let mut symbol_buffer = symbol.to_string();

        let span = Span {
            start: self.index,
            end: 0,
            start_pos: Position {
                line: self.line,
                column: self.column,
            },
            end_pos: Position::default(),
        };

        match symbol {
            END_OF_LINE => Ok(Token::new(
                symbol_buffer,
                TokenKind::Semicolon,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            OPEN_PARENTHESIS => Ok(Token::new(
                symbol_buffer,
                TokenKind::OpenParenthesis,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CLOSE_PARENTHESIS => Ok(Token::new(
                symbol_buffer,
                TokenKind::CloseParenthesis,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            OPEN_BRACKET => Ok(Token::new(
                symbol_buffer,
                TokenKind::OpenBracket,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CLOSE_BRACKET => Ok(Token::new(
                symbol_buffer,
                TokenKind::CloseBracket,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            OPEN_BRACE => Ok(Token::new(
                symbol_buffer,
                TokenKind::OpenBrace,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            CLOSE_BRACE => Ok(Token::new(
                symbol_buffer,
                TokenKind::CloseBrace,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            COMMA => Ok(Token::new(
                symbol_buffer,
                TokenKind::Comma,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            COLON => Ok(Token::new(
                symbol_buffer,
                TokenKind::Colon,
                span.set_end_from_values(self.index, self.line, self.column),
            )),
            STRING_DELIMITER => {
                while let Ok(c) = self.peek() {
                    if c == STRING_DELIMITER {
                        self.consume()?;
                        symbol_buffer.push(c);
                        return Ok(Token::new(
                            symbol_buffer,
                            TokenKind::StringLiteral,
                            span.set_end_from_values(self.index, self.line, self.column),
                        ));
                    }

                    if c == '\\' {
                        self.consume()?;
                        let ch = self.parse_escape_char()?;
                        symbol_buffer.push(ch);
                    } else {
                        symbol_buffer.push(self.consume()?);
                    }
                }

                return Err(self.generate_error(ErrorKind::UnterminatedString, Some(span)));
            }
            CHAR_DELIMITER => {
                let c = self.consume()?;

                if c == 'h' {
                    let is_heap_region =
                        self.peek_forward(1) == Ok('e') &&
                        self.peek_forward(2) == Ok('a') &&
                        self.peek_forward(3) == Ok('p') &&
                        self.peek_forward(4) == Ok(' ');

                    if is_heap_region {
                        self.consume()?;
                        self.consume()?;
                        self.consume()?;
                        self.consume()?;

                        return Ok(Token::new(
                            "heap".into(),
                            TokenKind::HeapRegion,
                            span.set_end_from_values(self.index, self.line, self.column),
                        ));
                    }
                }

                if c == '\\' {
                    let ch = self.parse_escape_char()?;
                    symbol_buffer.push(ch);
                } else if c != CHAR_DELIMITER {
                    symbol_buffer.push(c);
                } else {
                    return Err(self.generate_error(ErrorKind::InvalidChar(c.to_string()), Some(span)));
                }

                if self.consume()? == CHAR_DELIMITER {
                    symbol_buffer.push(CHAR_DELIMITER);
                    Ok(Token::new(
                        symbol_buffer,
                        TokenKind::CharLiteral,
                        span.set_end_from_values(self.index, self.line, self.column),
                    ))
                } else {
                    return Err(self.generate_error(ErrorKind::UnterminatedChar, Some(span)));
                }
            }
            _ => {
                return Err(self.generate_error(ErrorKind::UnrecognizedSymbol(symbol.to_string()), Some(span)))
            }
        }
    }
}

impl Lexer {
    pub fn new(program: String) -> Lexer {
        Lexer {
            lines: program.split("\n").map(|x| x.to_string()).collect(),
            source: program.chars().collect(),
            line: 1,
            column: 1,
            index: 0,
            tokens: vec![],
        }
    }

    pub fn tokenize(&mut self) -> Result<(), BoxedError> {
        while let Some(&char) = self.source.get(self.index) {
            if char.is_whitespace() {}
            else if char == '/' && matches!(self.peek(), Ok('/' | '*')) {
                match self.peek() {
                    Ok('/') => {
                        while matches!(self.peek(), Ok(c) if c != '\n') {
                            self.next_index();
                        }
                    },
                    Ok('*') => {
                        self.next_index();

                        'comment_loop: loop {
                            match self.peek() {
                                Ok('*') => {
                                    self.next_index();
                                    if self.peek() == Ok('/') {
                                        self.next_index();
                                        break 'comment_loop;
                                    }
                                }
                                Ok(_) => {
                                    self.next_index();
                                }
                                Err(_) => {
                                    break 'comment_loop;
                                }
                            }
                        }
                    },
                    _ => unreachable!(),
                }
            } else if char.is_operation() {
                let token = self.parse_operator()?;
                self.tokens.push(token);
            } else if char.is_alphabetic() {
                let token = self.parse_word()?;
                self.tokens.push(token);
            } else if char.is_numeric() {
                let token = self.parse_number()?;
                self.tokens.push(token);
            } else {
                let token = self.parse_symbol()?;
                self.tokens.push(token);
            }

            self.next_index();
        }

        self.tokens.push(Token::new(
            "".to_string(),
            TokenKind::EndOfFile,
            Span {
                start: self.index - 1,
                end: self.index - 1,
                start_pos: Position {
                    line: self.line,
                    column: if self.column == 1 { 1 } else { self.column - 1 },
                },
                end_pos: Position {
                    line: self.line,
                    column: if self.column == 1 { 1 } else { self.column - 1 },
                },
            },
        ));

        Ok(())
    }

    pub fn get_tokens(&self) -> &Vec<Token> {
        &self.tokens
    }

    pub fn extract(self) -> (Vec<String>, Vec<Token>) {
        (self.lines, self.tokens)
    }
}
