#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum LxRosePunctuation {
    /// `,`
    Comma,
    /// `.`
    Period,
    /// `:`
    Colon,
    /// `;`
    Semicolon,
    /// `!`
    Exclamation,
    /// `?`
    Question,
}

impl LxRosePunctuation {
    pub fn try_from_char(c: char) -> Option<Self> {
        match c {
            ',' => Some(Self::Comma),
            '.' => Some(Self::Period),
            ':' => Some(Self::Colon),
            ';' => Some(Self::Semicolon),
            '!' => Some(Self::Exclamation),
            '?' => Some(Self::Question),
            _ => None,
        }
    }
}
