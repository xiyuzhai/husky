use super::*;
use husky_text_protocol::offset::TextOffset;

impl<'a> TomlTokenIter<'a> {
    pub(crate) fn next_keylike(&mut self, start: TextOffset) -> TomlTokenData {
        while let Some(ch) = self.peek_char() {
            if !is_keylike(ch) {
                break;
            }
            self.next_char();
        }
        TomlTokenData::Word(Coword::from_ref(
            self.db,
            &self.input[TextOffsetRange::from(start..self.current())],
        ))
    }
}

pub(crate) fn is_keylike(ch: char) -> bool {
    ('A'..='Z').contains(&ch)
        || ('a'..='z').contains(&ch)
        || ('0'..='9').contains(&ch)
        || ch == '-'
        || ch == '_'
}
