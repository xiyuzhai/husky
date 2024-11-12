use crate::level::NamAstLevel;
use husky_text_protocol::{
    char::TextCharIter,
    paragraph::{Paragraph, ParagraphIter},
    span::TextSpan,
};

pub(crate) struct NamParagraph<'a> {
    pub(crate) lead: NamParagraphLead,
    pub(crate) content: &'a str,
    pub(crate) span: TextSpan,
}

impl<'a> From<Paragraph<'a>> for NamParagraph<'a> {
    fn from(paragraph: Paragraph<'a>) -> Self {
        Self {
            lead: paragraph.content.into(),
            content: paragraph.content,
            span: paragraph.span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NamParagraphLead {
    Chapter,
    Section,
    Subsection,
    Subsubsection,
    Notion,
    Semantics,
    Proposition,
    Theorem,
    HeavyArrow,
    Other,
}

impl NamParagraphLead {
    pub(crate) fn level(self) -> NamAstLevel {
        match self {
            NamParagraphLead::Chapter => NamAstLevel::Chapter,
            NamParagraphLead::Section => NamAstLevel::Section,
            NamParagraphLead::Subsection => NamAstLevel::Subsection,
            NamParagraphLead::Subsubsection => NamAstLevel::Subsubsection,
            NamParagraphLead::Notion
            | NamParagraphLead::Semantics
            | NamParagraphLead::Proposition
            | NamParagraphLead::Theorem
            | NamParagraphLead::HeavyArrow
            | NamParagraphLead::Other => NamAstLevel::Entry,
        }
    }
}

impl From<&str> for NamParagraphLead {
    fn from(content: &str) -> Self {
        let mut char_iter = TextCharIter::new(content);
        match char_iter.peek().expect("shouldn't be empty") {
            c if c.is_alphabetic() => match char_iter.next_str_slice_while(|c| c.is_alphabetic()) {
                "chapter" => NamParagraphLead::Chapter,
                "section" => NamParagraphLead::Section,
                "subsection" => NamParagraphLead::Subsection,
                "subsubsection" => NamParagraphLead::Subsubsection,
                "Notion" => NamParagraphLead::Notion,
                "Semantics" => NamParagraphLead::Semantics,
                "Proposition" => NamParagraphLead::Proposition,
                "Theorem" => NamParagraphLead::Theorem,
                _ => NamParagraphLead::Other,
            },
            '=' => {
                char_iter.eat_char();
                match char_iter.next() {
                    Some('>') => NamParagraphLead::HeavyArrow,
                    _ => NamParagraphLead::Other,
                }
            }
            _ => NamParagraphLead::Other,
        }
    }
}

#[test]
fn nam_paragraph_lead_from_str_works() {
    fn t(input: &str, expected: NamParagraphLead) {
        assert_eq!(
            NamParagraphLead::from(input),
            expected,
            "Failed on input: {}",
            input
        );
    }

    t("chapter", NamParagraphLead::Chapter);
    t("section", NamParagraphLead::Section);
    t("subsection", NamParagraphLead::Subsection);
    t("subsubsection", NamParagraphLead::Subsubsection);
    t("Notion", NamParagraphLead::Notion);
    t("Semantics", NamParagraphLead::Semantics);
    t("Proposition", NamParagraphLead::Proposition);
    t("Theorem", NamParagraphLead::Theorem);
    t("=>", NamParagraphLead::HeavyArrow);
    t("unknown", NamParagraphLead::Other);
    t("=", NamParagraphLead::Other); // Edge case: Just '=' without '>'
    t("subsubsection Android", NamParagraphLead::Subsubsection);
    t("section 5.1 Introduction", NamParagraphLead::Section);
    t("Notion of Identity", NamParagraphLead::Notion);
    t("Semantics & Meaning", NamParagraphLead::Semantics);
    t("Proposition about Equality", NamParagraphLead::Proposition);
    t("Theorem Pythagorean", NamParagraphLead::Theorem);
    t("chapter The Beginning", NamParagraphLead::Chapter);
    t("=> Implication", NamParagraphLead::HeavyArrow);
}

/// # iter

pub(crate) struct NamParagraphIter<'a> {
    paragraph_iter: ParagraphIter<'a>,
}

impl<'a> NamParagraphIter<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            paragraph_iter: ParagraphIter::new(input),
        }
    }
}

impl<'a> Iterator for NamParagraphIter<'a> {
    type Item = NamParagraph<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.paragraph_iter.next().map(Into::into)
    }
}
