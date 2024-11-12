pub mod delimiter;
pub mod ident;
pub mod keyword;
pub mod literal;
pub mod opr;
pub mod separator;

use self::{delimiter::*, ident::Ident, keyword::Keyword, literal::Literal, opr::Opr};
use crate::token::separator::Separator;
use crate::*;
use cybertron::seq::Seq;
use delimiter::{Delimiter, LeftDelimiter, RightDelimiter};
use husky_text_protocol::char::TextCharIter;
use opr::SuffixOpr;

/// The `Token` enum represents the various types of tokens that can be
/// identified during the lexical analysis phase of a compiler. Each variant
/// corresponds to a specific category of token that can be encountered
/// in the source code.
#[enum_class::from_variants]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Token {
    /// A literal value, which can be a number, string, or other primitive type.
    Literal(Literal),
    /// A reserved keyword in the language, such as `if`, `else`, `while`, etc.
    Keyword(Keyword),
    /// An identifier, typically representing variable names, function names,
    /// or other user-defined symbols.
    Ident(Ident),
    /// An operator, such as `+`, `-`, `*`, `==`, etc., representing mathematical
    /// or logical operations.
    Opr(Opr),
    /// A left delimiter, such as `(`, `{`, `[`, used to denote the beginning of
    /// a block, list, or expression.
    LeftDelimiter(LeftDelimiter),
    /// A right delimiter, such as `)`, `}`, `]`, used to denote the end of a
    /// block, list, or expression.
    RightDelimiter(RightDelimiter),
    /// A separator, such as `,` or `;`, used to separate elements in a list or
    /// statements in a block.
    Separator(Separator),
}

pub enum Convexity {
    Convex,
    Concave,
}

impl Token {
    pub fn repr(self) -> String {
        match self {
            Token::Literal(lit) => format!("{}", lit),
            Token::Keyword(kw) => format!("{}", kw.repr()),
            Token::Ident(ident) => format!("{}", ident.repr()),
            Token::Opr(opr) => format!("{}", opr.repr()),
            Token::LeftDelimiter(delimiter) => format!("{}", delimiter.repr()),
            Token::RightDelimiter(delimiter) => format!("{}", delimiter.repr()),
            Token::Separator(separator) => format!("{}", separator.repr()),
        }
    }

    pub fn repr_short(self) -> String {
        match self {
            Token::Literal(lit) => format!("{}", lit),
            Token::Keyword(kw) => format!("{}", kw.repr()),
            Token::Ident(ident) => format!("{}", ident.repr()),
            Token::Opr(opr) => format!("{}", opr.repr_short()),
            Token::LeftDelimiter(delimiter) => format!("{}", delimiter.repr()),
            Token::RightDelimiter(delimiter) => format!("{}", delimiter.repr()),
            Token::Separator(separator) => format!("{}", separator.repr()),
        }
    }

    pub fn right_convexity(self) -> Convexity {
        match self {
            Token::Literal(_) => Convexity::Convex,
            Token::Keyword(_) => Convexity::Concave,
            Token::Ident(_) => Convexity::Convex,
            Token::Opr(opr) => match opr {
                Opr::Prefix(_) => Convexity::Concave,
                Opr::Binary(_) => Convexity::Concave,
                Opr::Suffix(_) => Convexity::Convex,
            },
            Token::LeftDelimiter(_) => Convexity::Concave,
            Token::RightDelimiter(_) => Convexity::Convex,
            Token::Separator(_) => Convexity::Concave,
        }
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Literal(lit) => write!(f, "`{}`", lit),
            Token::Keyword(kw) => write!(f, "`{}`", kw.repr()),
            Token::Ident(ident) => write!(f, "`{}`", ident.repr()),
            Token::Opr(opr) => write!(f, "`{}`", opr.repr()),
            Token::LeftDelimiter(delimiter) => write!(f, "`{}`", delimiter.repr()),
            Token::RightDelimiter(delimiter) => write!(f, "`{}`", delimiter.repr()),
            Token::Separator(separator) => write!(f, "`{}`", separator.repr()),
        }
    }
}

pub fn tokenize(input: &str) -> Seq<Token> {
    Seq::new(Tokenizer::new(input).collect())
}

struct Tokenizer<'a> {
    chars: TextCharIter<'a>,
    last_token_right_convexity: Convexity,
}

impl<'a> Tokenizer<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            chars: TextCharIter::new(input),
            last_token_right_convexity: Convexity::Concave,
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_aux();
        if let Some(token) = token {
            self.last_token_right_convexity = token.right_convexity();
        }
        token
    }
}

/// # actions
impl<'a> Tokenizer<'a> {
    fn next_aux(&mut self) -> Option<Token> {
        match self.chars.next()? {
            ' ' | '\n' | '\t' => self.next(),
            '+' => match self.chars.peek() {
                Some('+') => {
                    self.chars.next();
                    Some(Opr::INCR.into())
                }
                _ => match self.last_token_right_convexity {
                    Convexity::Convex => Some(Opr::ADD.into()),
                    Convexity::Concave => Some(Opr::PLUS.into()),
                },
            },
            '-' => match self.chars.peek() {
                Some('-') => {
                    self.chars.next();
                    Some(Opr::DECR.into())
                }
                Some('>') => {
                    self.chars.next();
                    Some(Opr::LIGHT_ARROW.into())
                }
                _ => match self.last_token_right_convexity {
                    Convexity::Convex => Some(Opr::SUB.into()),
                    Convexity::Concave => Some(Opr::MINUS.into()),
                },
            },
            '*' => Some(Opr::MUL.into()),
            '/' => Some(Opr::DIV.into()),
            '=' => match self.chars.peek() {
                Some('=') => {
                    self.chars.next();
                    Some(Opr::EQ.into())
                }
                _ => Some(Opr::ASSIGN.into()),
            },
            ':' => match self.chars.peek() {
                Some(':') => {
                    self.chars.next();
                    Some(Opr::SCOPE_RESOLUTION.into())
                }
                _ => Some(Opr::TYPE_IS.into()),
            },
            '(' => Some(LPAR.into()),
            ')' => Some(RPAR.into()),
            '[' => Some(LBOX.into()),
            ']' => Some(RBOX.into()),
            '{' => Some(LCURL.into()),
            '}' => Some(RCURL.into()),
            ',' => Some(Separator::Comma.into()),
            ';' => Some(Separator::Semicolon.into()),
            '.' => {
                let ident = Ident::new(String::from(
                    self.chars
                        .next_str_slice_while(|c| c.is_alphanumeric() || c == '_'),
                ));
                Some(Opr::Suffix(SuffixOpr::Field(ident)).into())
            }
            c if c.is_alphabetic() || c == '_' => Some(self.next_keyword_or_ident(c)),
            c if c.is_numeric() => Some(self.next_numeric_literal(c)),
            c => todo!("c = `{c}`"),
        }
    }

    fn next_keyword_or_ident(&mut self, c: char) -> Token {
        let mut s = String::from(c);
        s += self
            .chars
            .next_str_slice_while(|c| c.is_alphanumeric() || c == '_');
        if let Some(keyword) = Keyword::new(&s) {
            return keyword.into();
        }
        Ident::new(s).into()
    }

    fn next_numeric_literal(&mut self, c: char) -> Token {
        let mut s = String::from(c);
        s += self.chars.next_str_slice_while(|c| c.is_numeric());
        let i: i32 = s.parse().unwrap();
        Token::Literal(Literal::Int(i))
    }
}

#[test]
fn tokenize_works() {
    fn t(input: &str, expect: Expect) {
        expect.assert_debug_eq(&tokenize(input));
    }
    t(
        "hello",
        expect![[r#"
        [`hello`]
    "#]],
    );
    t(
        "hello ",
        expect![[r#"
        [`hello`]
    "#]],
    );
    t(
        " hello ",
        expect![[r#"
        [`hello`]
    "#]],
    );
    t(
        " let hello = world",
        expect![[r#"
            [`let`, `hello`, `=`, `world`]
        "#]],
    );
    t(
        " let hello = 1",
        expect![[r#"
            [`let`, `hello`, `=`, `1`]
        "#]],
    );
    t(
        " let hello = world + 1",
        expect![[r#"
            [`let`, `hello`, `=`, `world`, `+(add)`, `1`]
        "#]],
    );
    t(
        "-1",
        expect![[r#"
            [`-(minus)`, `1`]
        "#]],
    );
    t(
        "1+-1",
        expect![[r#"
            [`1`, `+(add)`, `-(minus)`, `1`]
        "#]],
    );
    t(
        "1-1",
        expect![[r#"
            [`1`, `-(sub)`, `1`]
        "#]],
    );
    t(
        "x++",
        expect![[r#"
            [`x`, `++`]
        "#]],
    );
    t(
        "x--",
        expect![[r#"
            [`x`, `--`]
        "#]],
    );
    t(
        ".x",
        expect![[r#"
            [`.x`]
        "#]],
    );
    t(
        "A.x",
        expect![[r#"
            [`A`, `.x`]
        "#]],
    );
}
