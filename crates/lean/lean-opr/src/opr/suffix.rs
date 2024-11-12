use crate::precedence::LnPrecedenceRange;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LnSuffixOpr {}

impl LnSuffixOpr {
    pub fn fmt_str(self) -> &'static str {
        todo!()
    }

    pub fn precedence_range(self) -> LnPrecedenceRange {
        todo!()
    }
}
