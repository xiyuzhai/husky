use super::*;
use husky_text_protocol::{char::TextCharIter, offset::TextOffset, position::TextPosition};

#[derive(Clone)]
pub(crate) struct TomlTokenIter<'a> {
    pub(crate) db: &'a ::salsa::Db,
    pub(crate) input: &'a str,
    chars: TextCharIter<'a>,
}

impl<'a> Iterator for TomlTokenIter<'a> {
    type Item = TomlToken;

    fn next(&mut self) -> Option<Self::Item> {
        let (start_offset, start_position, c) = self.chars.next_char_with_offset_and_position()?;

        let variant = match c {
            '\n' => return self.next(),
            ' ' => return self.eat_whitespace_then_next(),
            '\t' => return self.eat_whitespace_then_next(),
            '#' => self.next_comment_token(),
            '=' => TomlSpecialToken::Equals.into(),
            '.' => TomlSpecialToken::Period.into(),
            ',' => TomlSpecialToken::Comma.into(),
            ':' => TomlSpecialToken::Colon.into(),
            '+' => TomlSpecialToken::Plus.into(),
            '{' => TomlSpecialToken::LeftCurly.into(),
            '}' => TomlSpecialToken::RightCurly.into(),
            '[' => TomlSpecialToken::LeftBox.into(),
            ']' => TomlSpecialToken::RightBox.into(),
            '\'' => self.next_literal_string(),
            '"' => self.next_basic_string(),
            ch if is_keylike(ch) => self.next_keylike(start_offset),
            ch => TomlTokenData::Err(TomlTokenError::UnexpectedChar(ch)),
        };

        Some(self.emit_token(start_offset, start_position, variant))
    }
}

impl<'a> TomlTokenIter<'a> {
    pub(crate) fn new(db: &'a ::salsa::Db, input: &'a str) -> Self {
        let mut t = TomlTokenIter {
            db,
            input,
            chars: TextCharIter::new(input),
        };
        // Eat utf-8 BOM
        t.try_eat_char('\u{feff}');
        t
    }

    pub(crate) fn current(&self) -> TextOffset {
        self.chars.current_offset()
    }

    pub(crate) fn emit_token(
        &self,
        start_offset: TextOffset,
        start_position: TextPosition,
        variant: TomlTokenData,
    ) -> TomlToken {
        TomlToken::new(
            (start_offset..self.chars.current_offset()).into(),
            (start_position..self.chars.current_position()).into(),
            variant,
        )
    }
}

impl<'a> TomlTokenIter<'a> {
    pub(crate) fn try_eat_char(&mut self, ch: char) -> bool {
        match self.chars.clone().next() {
            Some(ch2) if ch == ch2 => {
                self.next_char();
                true
            }
            _ => false,
        }
    }

    /// Peek one char without consuming it.
    pub(crate) fn peek_char(&self) -> Option<char> {
        self.chars.peek()
    }

    /// Take one char.
    pub(crate) fn next_char(&mut self) -> Option<char> {
        self.chars.next()
    }

    pub(crate) fn next_char_with_offset(&mut self) -> Option<(TextOffset, char)> {
        self.chars.next_char_with_offset()
    }
}

#[derive(Clone)]
pub(crate) struct CrlfFold<'a> {
    chars: std::str::CharIndices<'a>,
}

impl<'a> CrlfFold<'a> {
    fn new(chars: std::str::CharIndices<'a>) -> Self {
        Self { chars }
    }
}

impl<'a> Iterator for CrlfFold<'a> {
    type Item = (usize, char);

    fn next(&mut self) -> Option<(usize, char)> {
        self.chars.next().map(|(i, c)| {
            if c == '\r' {
                let mut attempt = self.chars.clone();
                if let Some((_, '\n')) = attempt.next() {
                    self.chars = attempt;
                    return (i, '\n');
                }
            }
            (i, c)
        })
    }
}
