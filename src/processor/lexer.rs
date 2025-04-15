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
    tokens: Vec<Token>
}

impl Lexer {
    pub fn new(program: String) -> Lexer {
        Lexer {
            source: program.chars().collect(),
            line: 1,
            char: 1,
            index: 0,
            tokens: vec![]
        }
    }

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

    /// Parses an operation.
    fn parse_operator(&mut self) -> Result<Token, LexerError> {
        let mut operator = self.source[self.index].to_string();

        match operator.chars().next().unwrap() {
            NEGATE_TOKEN => Ok(Token::new(operator, TokenType::Unary(Operation::Negate))),
            BITWISE_NEGATE_TOKEN => Ok(Token::new(operator, TokenType::Unary(Operation::BitwiseNegate))),
            ADD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::AddEq)
                    },
                    Ok(c) if c == ADD_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Unary(Operation::Increment)
                    },
                    _ => TokenType::Binary(Operation::Add),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            SUB_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::SubEq)
                    },
                    Ok(c) if c == SUB_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Unary(Operation::Decrement)
                    },
                    _ => TokenType::Binary(Operation::Sub),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            MUL_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::MulEq)
                    },
                    Ok(c) if c == MUL_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::Exp)
                    },
                    _ => TokenType::Binary(Operation::Mul),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            DIV_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::DivEq)
                    },
                    _ => TokenType::Binary(Operation::Div),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            MOD_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::ModEq)
                    },
                    _ => TokenType::Binary(Operation::Mod),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            BITWISE_AND_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_AND_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Conditional(Operation::And)
                    },
                    _ => TokenType::Binary(Operation::BitwiseAnd),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            BITWISE_OR_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == BITWISE_OR_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Conditional(Operation::Or)
                    },
                    _ => TokenType::Binary(Operation::BitwiseOr),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            BITWISE_XOR_TOKEN => Ok(Token::new(operator, TokenType::Binary(Operation::BitwiseXor))),
            ASSIGNMENT_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Conditional(Operation::Equivalence)
                    },
                    _ => TokenType::Binary(Operation::Assign),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            GREATER_THAN_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Conditional(Operation::Geq)
                    },
                    Ok(c) if c == GREATER_THAN_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::RightBitShift)
                    },
                    _ => TokenType::Conditional(Operation::GreaterThan),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            LESS_THAN_TOKEN => {
                let token_type = match self.peek() {
                    Ok(c) if c == ASSIGNMENT_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Conditional(Operation::Leq)
                    },
                    Ok(c) if c == LESS_THAN_TOKEN => {
                        operator.push(self.consume()?);
                        TokenType::Binary(Operation::LeftBitShift)
                    },
                    _ => TokenType::Conditional(Operation::LessThan),
                };
                
                Ok(Token::new(operator, token_type))                
            },
            _ => Err(LexerError::UnidentifiedError(self.line, self.char, operator))
        }
    }

    /// Parses a word.
    fn parse_word(&mut self) -> Result<Token, LexerError> {
        let mut word = self.source[self.index].to_string();
        while let Ok(char) = self.peek() && (char.is_alphanumeric() || char == '_') {
            self.next_index();
            word.push(self.source[self.index]);
        }

        match word.as_str() {
            _ => Ok(Token::new(word, TokenType::Identifier))
        }
    }

    /// Parses a number.
    fn parse_number(&mut self) -> Result<Token, LexerError> {
        let mut number_str = String::new();
        let mut has_decimal_point = false;
        let mut has_exponent = false;
    
        let first_char = self.source[self.index];
        number_str.push(first_char);
    
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
                        2 => NumberType::Binary,
                        8 => NumberType::Octal,
                        16 => NumberType::Hex,
                        _ => unreachable!(),
                    };

                    return Ok(Token::new(number_str, TokenType::Numeric(number_type)));
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
            NumberType::Float
        } else {
            NumberType::Decimal
        };
    
        Ok(Token::new(number_str, TokenType::Numeric(number_type)))
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
            }

            self.next_index();
        }

        Ok(())
    }
}

impl Lexer {
    pub fn get_tokens(&self) -> &Vec<Token> {
        &self.tokens
    }
}