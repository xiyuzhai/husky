pub mod delimiter;
pub mod ident;
pub mod label;
pub mod literal;

use self::{delimiter::LxLispDelimiter, ident::LxLispIdent, literal::LxLispLiteral};
use super::*;
use crate::idx::LxLispTokenIdx;
use coword::Coword;
use husky_text_protocol::{offset::TextOffsetRange, range::TextPositionRange};
use label::LxLispXlabel;
use latex_command::path::LxCommandName;
use ordered_float::NotNan;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxLispTokenData {
    Literal(LxLispLiteral),
    Ident(LxLispIdent),
    Xlabel(LxLispXlabel),
    LeftDelimiter(LxLispDelimiter),
    RightDelimiter(LxLispDelimiter),
    Command(LxCommandName),
    Comma,
}

impl<'a> LxLexer<'a> {
    pub fn next_lisp_token(&mut self) -> Option<(LxLispTokenIdx, LxLispTokenData)> {
        let (offset_range, range, token_data) = self.next_ranged_lisp_token_data()?;
        Some((
            self.alloc_lisp_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_ranged_lisp_token_data(
        &mut self,
    ) -> Option<(TextOffsetRange, TextPositionRange, LxLispTokenData)> {
        self.eat_spaces_and_tabs();
        let mut start_offset = self.chars.current_offset();
        let mut start_position = self.chars.current_position();
        let token_data = self.next_lisp_token_data()?;
        let end_offset = self.chars.current_offset();
        let range = TextPositionRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub fn peek_lisp_token_data(&mut self) -> Option<LxLispTokenData> {
        let chars = self.chars.clone();
        let (_, _, token_data) = self.next_ranged_lisp_token_data()?;
        self.chars = chars;
        Some(token_data)
    }

    pub(crate) fn next_lisp_token_data(&mut self) -> Option<LxLispTokenData> {
        Some(match self.chars.peek()? {
            '}' => return None,
            '\\' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some(c) => match c {
                        c if c.is_ascii_alphabetic() => {
                            let Ok(command_name) = LxCommandName::new2(
                                self.chars.next_str_slice_while(|c| c.is_ascii_alphabetic()),
                            ) else {
                                todo!()
                            };
                            LxLispTokenData::Command(command_name)
                        }
                        c => {
                            todo!()
                        }
                    },
                    None => todo!(),
                }
            }
            n if n.is_ascii_digit() => {
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
                        LxLispLiteral::Int(i)
                    }
                    1 => {
                        let f = match s.parse::<f64>() {
                            Ok(f) => f,
                            Err(e) => todo!("{}", e),
                        };
                        let f = match NotNan::new(f) {
                            Ok(f) => f,
                            Err(e) => todo!("{}", e),
                        };
                        LxLispLiteral::Float(f)
                    }
                    _ => unreachable!(),
                };
                LxLispTokenData::Literal(literal)
            }
            c if c.is_ascii_alphabetic() => {
                let ident = LxLispIdent::new(
                    self.chars
                        .next_str_slice_while(|c| c.is_ascii_alphanumeric() || c == '_'),
                );
                LxLispTokenData::Ident(ident)
            }
            '\'' => {
                self.chars.eat_char();
                let label =
                    LxLispXlabel::new(self.chars.next_str_slice_while(|c| {
                        c.is_ascii_alphanumeric() || c == '-' || c == ':'
                    }));
                LxLispTokenData::Xlabel(label)
            }
            '"' => {
                let mut data = String::new();
                self.chars.eat_char();
                loop {
                    let Some(c) = self.chars.next() else { todo!() };
                    match c {
                        '"' => break,
                        '\\' => {
                            let Some(c) = self.chars.next() else { todo!() };
                            match c {
                                '\\' | '"' => data.push(c),
                                _ => todo!(),
                            }
                        }
                        c => data.push(c),
                    }
                }
                LxLispTokenData::Literal(LxLispLiteral::String(Coword::new(data)))
            }
            c => {
                self.chars.eat_char();
                match c {
                    '(' => LxLispTokenData::LeftDelimiter(LxLispDelimiter::Parenthesis),
                    ')' => LxLispTokenData::RightDelimiter(LxLispDelimiter::Parenthesis),
                    '[' => LxLispTokenData::LeftDelimiter(LxLispDelimiter::Box),
                    ']' => LxLispTokenData::RightDelimiter(LxLispDelimiter::Box),
                    ',' => LxLispTokenData::Comma,
                    c => todo!("c: {}", c),
                }
            }
        })
    }
}
