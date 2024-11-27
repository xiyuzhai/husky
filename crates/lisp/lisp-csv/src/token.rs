use crate::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvToken {
    Literal(LpCsvLiteral),
    Ident(String),
    Connector(LpCsvConnector),
    Separator(LpCsvSeparator),
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LpCsvConnector {
    /// `.`
    Dot,
    /// `::`
    ColonColon,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LpCsvSeparator {
    /// `,`
    Comma,
    /// `;`
    Semicolon,
    /// `:`
    Colon,
    /// `=`
    Equal,
    /// `==`
    EqualEqual,
    /// `:=`
    ColonEqual,
    /// `|`
    Vert,
    /// `||`
    VertVert,
    /// `->`
    LightArrow,
    /// `=>`
    HeavyArrow,
}

impl<'a> LpCsvParser<'a> {
    pub(crate) fn next_token(&mut self) -> Option<LpCsvToken> {
        self.ignore_whitespaces_and_tabs_and_comments();
        match self.chars.peek()? {
            '"' => {
                self.chars.eat_char();
                let mut s = String::new();
                loop {
                    match self.chars.next() {
                        Some('"') => break,
                        Some('\\') => match self.chars.next() {
                            Some('n') => s.push('\n'),
                            Some('t') => s.push('\t'),
                            Some('\\') => s.push('\\'),
                            Some('"') => s.push('"'),
                            Some(c) => todo!("c: `{c:?}`"),
                            None => todo!(),
                        },
                        Some(c) => s.push(c),
                        None => todo!(),
                    }
                }
                Some(LpCsvToken::Literal(LpCsvLiteral::String(s)))
            }
            c if c.is_ascii_digit() => {
                let mut dot_count = 0;
                let s = self.chars.next_str_slice_while(|c| {
                    if c == '.' {
                        dot_count += 1;
                    }
                    (c.is_ascii_digit() || c == '.') && dot_count < 2
                });
                let literal = match dot_count {
                    0 => {
                        let i = match s.parse() {
                            Ok(i) => i,
                            Err(e) => todo!("{}", e),
                        };
                        LpCsvLiteral::Integer(i)
                    }
                    1 => {
                        let f = match s.parse::<f64>() {
                            Ok(f) => f,
                            Err(e) => todo!("{}", e),
                        };
                        let f = OrderedFloat(f);
                        LpCsvLiteral::Float(f)
                    }
                    _ => unreachable!(),
                };
                Some(LpCsvToken::Literal(literal))
            }
            c if c.is_ascii_alphabetic() => {
                let ident = self
                    .chars
                    .next_str_slice_while(|c| c.is_ascii_alphanumeric() || c == '_')
                    .to_string();
                Some(LpCsvToken::Ident(ident))
            }
            '(' => {
                self.chars.eat_char();
                Some(LpCsvToken::LeftParen)
            }
            ')' => {
                self.chars.eat_char();
                Some(LpCsvToken::RightParen)
            }
            '[' => {
                self.chars.eat_char();
                Some(LpCsvToken::LeftBracket)
            }
            ']' => {
                self.chars.eat_char();
                Some(LpCsvToken::RightBracket)
            }
            '\n' => None,
            ',' => {
                self.chars.eat_char();
                Some(LpCsvToken::Separator(LpCsvSeparator::Comma))
            }
            ';' => {
                self.chars.eat_char();
                Some(LpCsvToken::Separator(LpCsvSeparator::Semicolon))
            }
            ':' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some('=') => {
                        self.chars.eat_char();
                        Some(LpCsvToken::Separator(LpCsvSeparator::ColonEqual))
                    }
                    Some(':') => {
                        self.chars.eat_char();
                        Some(LpCsvToken::Connector(LpCsvConnector::ColonColon))
                    }
                    _ => Some(LpCsvToken::Separator(LpCsvSeparator::Colon)),
                }
            }
            '=' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some('=') => {
                        self.chars.eat_char();
                        Some(LpCsvToken::Separator(LpCsvSeparator::EqualEqual))
                    }
                    Some('>') => {
                        self.chars.eat_char();
                        Some(LpCsvToken::Separator(LpCsvSeparator::LightArrow))
                    }
                    _ => Some(LpCsvToken::Separator(LpCsvSeparator::Equal)),
                }
            }
            '|' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some('|') => {
                        self.chars.eat_char();
                        Some(LpCsvToken::Separator(LpCsvSeparator::VertVert))
                    }
                    _ => Some(LpCsvToken::Separator(LpCsvSeparator::Vert)),
                }
            }
            '.' => {
                self.chars.eat_char();
                Some(LpCsvToken::Connector(LpCsvConnector::Dot))
            }
            c => todo!("c: `{c:?}`"),
        }
    }

    pub(crate) fn peek_token(&mut self) -> Option<LpCsvToken> {
        let chars = self.chars.clone();
        let token = self.next_token();
        self.chars = chars;
        token
    }

    pub(crate) fn eat_token(&mut self) {
        let _ = self.next_token();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn comment_works() {}
}
