use self::{level::NamAstLevel, paragraph::NamParagraph};
use super::*;

impl<'a> NamParser<'a> {
    pub(crate) fn parse_division_ast(
        &mut self,
        kind: NamDivisionKind,
        paragraph: NamParagraph,
    ) -> NamAstData {
        let level = kind.level();
        let items = self.with_level(level, |slf| slf.parse_asts());
        NamAstData::Division { kind, items }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum NamDivisionKind {
    Chapter,
    Section,
    Subsection,
    Subsubsection,
}

impl NamDivisionKind {
    fn level(self) -> NamAstLevel {
        match self {
            NamDivisionKind::Chapter => NamAstLevel::Chapter,
            NamDivisionKind::Section => NamAstLevel::Section,
            NamDivisionKind::Subsection => NamAstLevel::Subsection,
            NamDivisionKind::Subsubsection => NamAstLevel::Subsubsection,
        }
    }
}
