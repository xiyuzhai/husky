use visored_opr::precedence::VdPrecedence;

use super::*;

#[floated(constructor = pub new)]
pub struct VdBsqInSet<'sess> {
    pub element: VdBsqTerm<'sess>,
    pub set: VdBsqTerm<'sess>,
}

impl<'sess> From<VdBsqInSet<'sess>> for VdBsqTerm<'sess> {
    fn from(value: VdBsqInSet<'sess>) -> Self {
        VdBsqTerm::Prop(value.into())
    }
}

impl<'sess> VdBsqInSet<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let outer_precedence = VdPrecedence::RELATION;
        if precedence_range.contains(outer_precedence) {
            self.show_fmt_inner(precedence_range, f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(precedence_range, f)?;
            f.write_str(")")
        }
    }

    fn show_fmt_inner(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.element().show_fmt(precedence_range, f)?;
        f.write_str(" ∈ ")?;
        self.set().show_fmt(precedence_range, f)
    }
}
