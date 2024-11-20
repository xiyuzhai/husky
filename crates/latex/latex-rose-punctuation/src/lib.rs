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
    /// `{`
    LeftCurl,
    /// `}`
    RightCurl,
    /// `[`
    LeftBox,
    /// `]`
    RightBox,
    /// `\\`
    EscapedBackslash,
    /// `\{`
    EscapedLcurl,
    /// `\}`
    EscapedRcurl,
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

    pub fn as_str(&self) -> &'static str {
        match self {
            LxRosePunctuation::Comma => ",",
            LxRosePunctuation::Period => ".",
            LxRosePunctuation::Colon => ":",
            LxRosePunctuation::Semicolon => ";",
            LxRosePunctuation::Exclamation => "!",
            LxRosePunctuation::Question => "?",
            LxRosePunctuation::LeftCurl => "{",
            LxRosePunctuation::RightCurl => "}",
            LxRosePunctuation::LeftBox => "[",
            LxRosePunctuation::RightBox => "]",
            LxRosePunctuation::EscapedBackslash => "\\",
            LxRosePunctuation::EscapedLcurl => "{",
            LxRosePunctuation::EscapedRcurl => "}",
        }
    }
}

impl std::fmt::Display for LxRosePunctuation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
