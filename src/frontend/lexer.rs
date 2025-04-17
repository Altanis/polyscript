use crate::utils::{error::LexerError, token::*};

trait CharClassifier {
    fn is_operation(self) -> bool;
    fn valid_alphabetic_hex(self) -> bool;
}

impl CharClassifier for char {
    fn is_operation(self) -> bool {
        matches!(self,
            NEGATE_TOKEN | BITWISE_NEGATE_TOKEN | ADD_TOKEN | SUB_TOKEN 
            | MUL_TOKEN | DIV_TOKEN | MOD_TOKEN | BITWISE_AND_TOKEN 
            | BITWISE_OR_TOKEN | BITWISE_XOR_TOKEN | ASSIGNMENT_TOKEN | GREATER_THAN_TOKEN | LESS_THAN_TOKEN
        )
    }

    fn valid_alphabetic_hex(self) -> bool {
        matches!(self.to_ascii_lowercase(), 'a' | 'b' | 'c' | 'd' | 'e' | 'f')
    }
}

pub struct Lexer {
    /// The source program, as characters.
    source: Vec<char>,
    /// The line the lexer is reading.
    line: usize,
    /// The index in the line the lexer is reading.
    char: usize,
    /// The index in the source the lexer is reading.
    index: usize,
    /// The tokens collected from the source.
    tokens: Vec<Token>,
    /// A temporary span used while parsing a token.
    temp_span: Span
}

impl Lexer {
    /// Goes to the next line.
    fn next_line(&mut self) {
        self.line += 1;
        self.char = 1;
    }

    /// Goes to the next index.
    fn next_index(&mut self) {
        self.index += 1;
        self.char += 1;
    }

    /// Peeks at the next character.
    fn peek(&self) -> Result<char, LexerError> {
        self.source.get(self.index + 1).ok_or(LexerError::UnexpectedEOF(self.line, self.char)).copied()
    }

    /// Consumes the next character.
    fn consume(&mut self) -> Result<char, LexerError> {
        self.next_index();
        self.source.get(self.index).ok_or(LexerError::UnexpectedEOF(self.line, self.char)).copied()
    }

    /// Creates a new temporary span.
    fn create_span(&mut self) {
        self.temp_span = Span {
            start: self.index,
            end: 0,
            line: self.line,
            column: self.char
        }
    }

    /// Finalizes the span.
    fn finalize_span(&mut self) -> Span {
        self.temp_span.end = self.index;
        self.temp_span.clone()
    }
}

impl Lexer {
    /// Parses an operation.
    fn parse_operator(&mut self) -> Result<Token, LexerError> {
        let mut operator = self.source[self.index].to_string();
        self.create_span();

        match operator.chars().next().unwrap() {
            NEGATE_TOKEN => Ok(Token::new(operator, TokenKind::Unary(Operation::Negate), self.finalize_span())),
            BITWISE_NEGATE_TOKEN => Ok(Token::new(operator, TokenKind::Unary(Operation::BitwiseNegate), self.finalize_span())),
            ADD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::AddEq)
                    },
                    Ok(c) if c == ADD_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Unary(Operation::Increment)
                    },
                    _ => TokenKind::Binary(Operation::Add),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            SUB_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::SubEq)
                    },
                    Ok(c) if c == SUB_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Unary(Operation::Decrement)
                    },
                    _ => TokenKind::Binary(Operation::Sub),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            MUL_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::MulEq)
                    },
                    Ok(c) if c == MUL_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::Exp)
                    },
                    _ => TokenKind::Binary(Operation::Mul),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            DIV_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::DivEq)
                    },
                    _ => TokenKind::Binary(Operation::Div),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            MOD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::ModEq)
                    },
                    _ => TokenKind::Binary(Operation::Mod),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            BITWISE_AND_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_AND_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Conditional(Operation::And)
                    },
                    _ => TokenKind::Binary(Operation::BitwiseAnd),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            BITWISE_OR_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_OR_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Conditional(Operation::Or)
                    },
                    _ => TokenKind::Binary(Operation::BitwiseOr),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            BITWISE_XOR_TOKEN => Ok(Token::new(operator, TokenKind::Binary(Operation::BitwiseXor), self.finalize_span())),
            ASSIGNMENT_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Conditional(Operation::Equivalence)
                    },
                    _ => TokenKind::Binary(Operation::Assign),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            GREATER_THAN_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Conditional(Operation::Geq)
                    },
                    Ok(c) if c == GREATER_THAN_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::RightBitShift)
                    },
                    _ => TokenKind::Conditional(Operation::GreaterThan),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            LESS_THAN_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Conditional(Operation::Leq)
                    },
                    Ok(c) if c == LESS_THAN_TOKEN => {
                        operator.push(self.consume()?);
                        TokenKind::Binary(Operation::LeftBitShift)
                    },
                    _ => TokenKind::Conditional(Operation::LessThan),
                };
                
                Ok(Token::new(operator, token_type, self.finalize_span()))                
            },
            _ => Err(LexerError::UnidentifiedError(self.line, self.char, operator))
        }
    }

    /// Parses a word.
    fn parse_word(&mut self) -> Result<Token, LexerError> {
        let mut word = self.source[self.index].to_string();
        self.create_span();

        while let Ok(char) = self.peek() && (char.is_alphanumeric() || char == '_') {
            self.next_index();
            word.push(self.source[self.index]);
        }

        match word.as_str() {
            INT_TYPE | FLOAT_TYPE | BOOL_TYPE | STRING_TYPE | VOID_TYPE => {
                Ok(Token::new(word, TokenKind::Kind, self.finalize_span()))
            }
            LET_KEYWORD => Ok(Token::new(word, TokenKind::VariableDeclaration(true), self.finalize_span())),
            CONST_KEYWORD => Ok(Token::new(word, TokenKind::VariableDeclaration(false), self.finalize_span())),
            CLASS_KEYWORD => Ok(Token::new(word, TokenKind::ClassDeclaration, self.finalize_span())),
            OVERRIDE_KEYWORD => Ok(Token::new(word, TokenKind::Override, self.finalize_span())),
            TRUE_KEYWORD | FALSE_KEYWORD => Ok(Token::new(word, TokenKind::Boolean, self.finalize_span())),
            FN_KEYWORD => Ok(Token::new(word, TokenKind::FunctionDeclaration, self.finalize_span())),
            FOR_KEYWORD => Ok(Token::new(word, TokenKind::Loop(LoopKind::For), self.finalize_span())),
            WHILE_KEYWORD => Ok(Token::new(word, TokenKind::Loop(LoopKind::While), self.finalize_span())),
            RETURN_KEYWORD => Ok(Token::new(word, TokenKind::ControlFlow(ControlFlowKind::Return), self.finalize_span())),
            BREAK_KEYWORD => Ok(Token::new(word, TokenKind::ControlFlow(ControlFlowKind::Break), self.finalize_span())),
            CONTINUE_KEYWORD => Ok(Token::new(word, TokenKind::ControlFlow(ControlFlowKind::Continue), self.finalize_span())),
            THROW_KEYWORD => Ok(Token::new(word, TokenKind::ControlFlow(ControlFlowKind::Throw), self.finalize_span())),
            IF_KEYWORD => Ok(Token::new(word, TokenKind::If, self.finalize_span())),
            ELSE_KEYWORD => Ok(Token::new(word, TokenKind::Else, self.finalize_span())),
            _ => Ok(Token::new(word, TokenKind::Identifier, self.finalize_span()))   
        }
    }

    /// Parses a number.
    fn parse_number(&mut self) -> Result<Token, LexerError> {
        let mut number_str = String::new();
        let mut has_decimal_point = false;
        let mut has_exponent = false;
    
        let first_char = self.source[self.index];
        number_str.push(first_char);
        self.create_span();
    
        if first_char == '0' {
            if let Ok(next_char) = self.peek() {
                if let Some(base) = match next_char.to_ascii_lowercase() {
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
                        return Err(LexerError::InvalidDigit(self.line, self.char, invalid_char));
                    }

                    let number_type = match base {
                        2 => NumberKind::Binary,
                        8 => NumberKind::Octal,
                        16 => NumberKind::Hex,
                        _ => unreachable!(),
                    };

                    return Ok(Token::new(number_str, TokenKind::Numeric(number_type), self.finalize_span()));
                }
            }
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

                if let Ok(sign) = self.peek() {
                    if sign == '+' || sign == '-' {
                        number_str.push(self.consume()?);
                    }
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
                    return Err(LexerError::InvalidDigit(self.line, self.char, invalid_char));
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
    
        Ok(Token::new(number_str, TokenKind::Numeric(number_type), self.finalize_span()))
    }

    fn parse_symbol(&mut self) -> Result<Token, LexerError> {
        let symbol = self.source[self.index];
        self.create_span();

        match symbol {
            END_OF_LINE => Ok(Token::new(symbol.to_string(), TokenKind::EndOfLine, self.finalize_span())),
            OPEN_PARENTHESIS => Ok(Token::new(symbol.to_string(), TokenKind::OpenParenthesis, self.finalize_span())),
            CLOSE_PARENTHESIS => Ok(Token::new(symbol.to_string(), TokenKind::CloseParenthesis, self.finalize_span())),
            OPEN_BRACKET => Ok(Token::new(symbol.to_string(), TokenKind::OpenBracket, self.finalize_span())),
            CLOSE_BRACKET => Ok(Token::new(symbol.to_string(), TokenKind::CloseBracket, self.finalize_span())),
            OPEN_CURLY_BRACKET => Ok(Token::new(symbol.to_string(), TokenKind::OpenCurlyBracket, self.finalize_span())),
            CLOSE_CURLY_BRACKET => Ok(Token::new(symbol.to_string(), TokenKind::CloseCurlyBracket, self.finalize_span())),
            COMMA => Ok(Token::new(symbol.to_string(), TokenKind::Comma, self.finalize_span())),
            COLON => Ok(Token::new(symbol.to_string(), TokenKind::Colon, self.finalize_span())),
            _ => Err(LexerError::UnidentifiedError(self.line, self.char, symbol.to_string()))
        }
    }
}

impl Lexer {
    pub fn new(program: String) -> Lexer {
        Lexer {
            source: program.chars().collect(),
            line: 1,
            char: 1,
            index: 0,
            tokens: vec![],
            temp_span: Span::default()
        }
    }
    
    pub fn tokenize(&mut self) -> Result<(), LexerError> {
        while let Some(&char) = self.source.get(self.index) {
            if char.is_whitespace() {
                if char == '\n' { self.next_line(); }
            } else if char == COMMENT_TOKEN {
                while let Ok(c) = self.peek() {
                    if c == '\n' { break; }
                    else { self.next_index(); }
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

        self.tokens.push(Token::new("".to_string(), TokenKind::EOF, Span::default()));

        Ok(())
    }

    pub fn get_tokens(&self) -> &Vec<Token> {
        &self.tokens
    }
}