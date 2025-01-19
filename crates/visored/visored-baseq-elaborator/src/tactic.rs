pub mod assumption_or_trivial;
pub mod comm_ring;
pub mod kurapika;
pub mod library_search;
pub mod litnum_estimate;
pub mod litnum_reduce;

use crate::{
    elaborator::VdBsqElaboratorInner,
    expr::VdBsqExpr,
    hypothesis::{contradiction::VdBsqHypothesisResult, VdBsqHypothesisIdx},
    *,
};
use alt_option::AltOption;
use miracle::HasMiracleFull;

#[derive(Debug, PartialEq, Eq)]
pub enum VdBsqTactic {
    AssumptionOrTrivial,
    Kurapika,
    LibrarySearch,
    CommRing,
    LitnumReduce,
    LitnumEstimate,
}

// Trivial tactics are not tracked
#[derive(Debug, PartialEq, Eq)]
pub enum VdBsqTacticCall {
    Assumption,
    TermTrivial,
    Kurapika,
    LibrarySearch,
    CommRing,
    LitnumReduce,
    LitnumEstimate,
}

impl VdBsqTactic {
    pub fn run<'db, 'sess>(
        &self,
        prop: VdBsqExpr<'sess>,
        elaborator: &mut VdBsqElaboratorInner<'db, 'sess>,
    ) -> Mhr<'sess> {
        match self {
            VdBsqTactic::AssumptionOrTrivial => elaborator.assumption_or_trivial(prop),
            VdBsqTactic::Kurapika => elaborator.kurapika(prop),
            VdBsqTactic::LibrarySearch => elaborator.library_search(prop),
            VdBsqTactic::CommRing => elaborator.comm_ring(prop),
            VdBsqTactic::LitnumReduce => elaborator.litnum_reduce(prop),
            VdBsqTactic::LitnumEstimate => elaborator.litnum_estimate(prop),
        }
    }
}

impl VdBsqTacticCall {
    pub fn wrap<'db, 'sess, R>(self, m: impl ElabM<'db, 'sess, R>) -> impl ElabM<'db, 'sess, R>
    where
        'db: 'sess,
    {
        call::stack::with_call(self, m)
    }
}
