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
