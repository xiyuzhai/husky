use std::borrow::Cow;

#[derive(Debug)]
pub enum VfsEdit<'a> {
    InsertString {
        position: usize,
        insertion: Cow<'a, str>,
    },
    DeleteToEof {
        position: usize,
    },
    DeleteToEol {
        position: usize,
        delete_eol: bool,
    },
}

impl<'a> VfsEdit<'a> {
    pub(super) fn apply(self, text: &str) -> String {
        match self {
            VfsEdit::InsertString {
                position,
                insertion,
            } => {
                let mut result = String::new();
                for (i, ch) in text.char_indices() {
                    if i == position {
                        result += &insertion
                    }
                    result.push(ch)
                }
                result
            }
            VfsEdit::DeleteToEof { position } => {
                let mut result = String::new();
                for (i, ch) in text.char_indices() {
                    if i == position {
                        break;
                    }
                    result.push(ch)
                }
                result
            }
            VfsEdit::DeleteToEol {
                position,
                delete_eol,
            } => {
                let mut result = String::new();
                let mut char_indices = text.char_indices().peekable();
                while let Some((i, ch)) = char_indices.next() {
                    if i == position {
                        break;
                    }
                    result.push(ch)
                }
                while let Some((_, ch)) = char_indices.next() {
                    if ch == '\n' {
                        break;
                    } else if ch == '\r' {
                        match char_indices.peek() {
                            Some((_, '\n')) => {
                                char_indices.next();
                            }
                            _ => (),
                        }
                        break;
                    }
                }
                if !delete_eol {
                    result.push('\n')
                }
                while let Some((_, ch)) = char_indices.next() {
                    result.push(ch)
                }
                result
            }
        }
    }
}
