pub mod iff;
pub mod in_set;
pub mod num_chain;
pub mod num_relation;

use self::{iff::*, in_set::*, num_chain::*, num_relation::*};
use super::*;

#[enum_class::from_variants]
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqPropTerm<'sess> {
    NumRelation(VdBsqNumRelation<'sess>),
    NumChain(VdBsqNumChain<'sess>),
    Trivial(bool),
    InSet(VdBsqInSet<'sess>),
    Iff(VdBsqIff<'sess>),
}

impl<'sess> VdBsqPropTerm<'sess> {
    pub const TRUE: Self = Self::Trivial(true);
    pub const FALSE: Self = Self::Trivial(false);
}

impl<'sess> std::fmt::Debug for VdBsqPropTerm<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("PropTerm(`")?;
        self.show_fmt(VdPrecedenceRange::Any, f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdBsqPropTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqPropTerm::NumRelation(slf) => slf.show_fmt(precedence_range, f),
            VdBsqPropTerm::NumChain(slf) => slf.show_fmt(precedence_range, f),
            VdBsqPropTerm::Trivial(slf) => write!(f, "{}", slf),
            VdBsqPropTerm::InSet(slf) => slf.show_fmt(precedence_range, f),
            VdBsqPropTerm::Iff(vd_bsq_iff) => todo!(),
        }
    }
}

impl<'db, 'sess> VdBsqPropTerm<'sess> {
    pub(crate) fn expr(self, elr: &mut VdBsqElaboratorInner<'db, 'sess>) -> VdBsqExpr<'sess> {
        match self {
            VdBsqPropTerm::NumRelation(num_relation) => num_relation.expr(elr),
            VdBsqPropTerm::NumChain(num_chain) => num_chain.expr(elr),
            VdBsqPropTerm::Trivial(b) => {
                let path = match b {
                    true => VdItemPath::TRUE,
                    false => todo!(),
                };
                elr.mk_expr(VdBsqExprData::ItemPath(path), elr.ty_menu().prop)
            }
            VdBsqPropTerm::InSet(_) => todo!(),
            VdBsqPropTerm::Iff(vd_bsq_iff) => todo!(),
        }
    }
}
