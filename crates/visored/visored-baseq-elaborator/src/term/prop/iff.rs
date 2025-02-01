use super::*;

#[floated]
pub struct VdBsqIff<'sess> {
    pub lhs: VdBsqPropTerm<'sess>,
    pub rhs: VdBsqPropTerm<'sess>,
}

impl<'db, 'sess> VdBsqIff<'sess> {
    pub fn new(
        lhs: VdBsqPropTerm<'sess>,
        rhs: VdBsqPropTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqPropTerm<'sess> {
        if lhs == rhs {
            return VdBsqPropTerm::TRUE;
        }
        Self::new_inner(lhs, rhs, db).into()
    }
}
