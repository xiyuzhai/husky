pub mod in_set;
pub mod num_chain;
pub mod num_relation;

use self::{in_set::*, num_chain::*, num_relation::*};
use super::*;

#[enum_class::from_variants]
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqPropTerm<'sess> {
    NumRelation(VdBsqNumRelation<'sess>),
    NumChain(VdBsqNumChain<'sess>),
    Trivial(bool),
    InSet(VdBsqInSet<'sess>),
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
        }
    }
}

impl<'db, 'sess> VdBsqPropTerm<'sess> {
    pub(crate) fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprFld<'sess> {
        match self {
            VdBsqPropTerm::NumRelation(num_relation) => num_relation.expr(elr, hc),
            VdBsqPropTerm::NumChain(num_chain) => num_chain.expr(elr, hc),
            VdBsqPropTerm::Trivial(b) => {
                let path = match b {
                    true => VdItemPath::TRUE,
                    false => todo!(),
                };
                elr.mk_expr(VdBsqExprData::ItemPath(path), elr.ty_menu().prop)
            }
            VdBsqPropTerm::InSet(_) => todo!(),
        }
    }
}
