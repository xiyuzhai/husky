pub mod num_chain;
pub mod num_relation;

use self::{num_chain::*, num_relation::*};
use super::*;

#[enum_class::from_variants]
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqPropTerm<'sess> {
    NumRelation(VdBsqNumRelation<'sess>),
    NumChain(VdBsqNumChain<'sess>),
    Trivial(bool),
    InSet,
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
            VdBsqPropTerm::NumRelation(term) => term.show_fmt(precedence_range, f),
            VdBsqPropTerm::NumChain(_) => todo!(),
            VdBsqPropTerm::Trivial(b) => write!(f, "{}", b),
            VdBsqPropTerm::InSet => todo!(),
        }
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_prop_data(
        &self,
        prop: VdBsqPropTerm<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprData {
        match prop {
            VdBsqPropTerm::NumRelation(num_relation) => {
                self.transcribe_num_relation_data(num_relation, hypothesis_constructor)
            }
            VdBsqPropTerm::NumChain(num_chain) => {
                self.transcribe_num_chain_data(num_chain, hypothesis_constructor)
            }
            VdBsqPropTerm::Trivial(b) => {
                let path = match b {
                    true => VdItemPath::TRUE,
                    false => todo!(),
                };
                VdMirExprData::ItemPath(path)
            }
            VdBsqPropTerm::InSet => todo!(),
        }
    }
}
