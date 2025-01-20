pub mod neg;
pub mod product;
pub mod sub;
pub mod sum;

use self::{neg::*, product::*, sub::*, sum::*};
use super::*;
use crate::{
    derivation::VdMirDerivationIdx,
    expr::VdMirExprData,
    helpers::compare::{assert_deep_eq, vd_mir_expr_deep_eq},
    hypothesis::constructor::expr::ds,
};
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;
use visored_term::term::literal::VdLiteral;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Reflection,
    NumComparison {
        lhs_minus_rhs: VdMirTermDerivationIdx,
    },
    SubEqsAddNeg {
        add_neg: VdMirTermDerivationIdx,
    },
    LiteralAddLiteral {
        lopd: VdLiteral,
        ropd: VdLiteral,
    },
    /// derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
    AddEq {
        lopd: VdMirTermDerivationIdx,
        ropd: VdMirTermDerivationIdx,
        merge: VdMirTermDerivationIdx,
    },
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
    NegLiteral,
    /// derive `a + c => c + 1 * a` if `a` is an atom and `c` is a nonzero literal or summand with different stem
    AtomAddSwap,
    LiteralMul,
    MulEq {
        lopd: VdMirTermDerivationIdx,
        ropd: VdMirTermDerivationIdx,
        merge: VdMirTermDerivationIdx,
    },
    AtomMulSwap,
    /// derive `1 * b => b`
    OneMulAtom,
    /// derive `c * b => c * b^1` if `c` is a constant
    NonOneLiteralMulAtom,
    /// derive `c + a => c + 1 * a` if `a` is an atom and `c` is a nonzero literal or summand with different stem
    NonZeroLiteralAddAtom,
    /// derive `c + 0 => c`
    NfAddZero,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct VdMirTermDerivationIdx(VdMirDerivationIdx);

impl std::ops::Deref for VdMirTermDerivationIdx {
    type Target = VdMirDerivationIdx;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn alloc_term_derivation(
        &mut self,
        prop: VdMirExprIdx,
        construction: VdMirTermDerivationConstruction,
    ) -> VdMirTermDerivationIdx {
        let idx = self.alloc_derivation(prop, construction.into());
        VdMirTermDerivationIdx(idx)
    }
}

impl VdMirTermDerivationIdx {
    pub fn prop<'db, 'a, Src>(self, hc: &'a VdMirHypothesisConstructor<'db, Src>) -> VdMirExprIdx {
        hc.derivation_arena()[*self].prop()
    }

    pub fn construction<'db, 'a, Src>(
        self,
        hc: &'a VdMirHypothesisConstructor<'db, Src>,
    ) -> &'a VdMirTermDerivationConstruction {
        match hc.derivation_arena()[*self].construction() {
            VdMirDerivationConstruction::Ring(_) => unreachable!(),
            VdMirDerivationConstruction::Term(construction) => construction,
        }
    }
}

impl VdMirTermDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        let expr_arena = hc.expr_arena();
        let VdMirExprData::ChainingSeparatedList {
            leader: lhs,
            ref followers,
            joined_signature: None,
        } = *expr_arena[prop].data()
        else {
            unreachable!()
        };
        let (signature, rhs) = followers[0];
        match *self {
            VdMirTermDerivationConstruction::Reflection => {
                check_reflection(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => {
                check_literal_add_literal(lhs, rhs, hc)
            }
            VdMirTermDerivationConstruction::NumComparison { lhs_minus_rhs } => {
                check_num_comparison(lhs, signature, rhs, lhs_minus_rhs, hc)
            }
            VdMirTermDerivationConstruction::SubEqsAddNeg { add_neg } => {
                check_sub_eqs_add_neg(lhs, signature, rhs, add_neg, hc)
            }
            VdMirTermDerivationConstruction::AdditionInterchange => {
                check_add_interchange(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
            VdMirTermDerivationConstruction::NegLiteral => {
                check_neg_literal(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::AddEq {
                lopd, ropd, merge, ..
            } => check_add_eq(lhs, signature, rhs, lopd, ropd, merge, hc),
            VdMirTermDerivationConstruction::AtomAddSwap => {
                check_atom_add_constant(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::LiteralMul => todo!(),
            VdMirTermDerivationConstruction::MulEq { lopd, ropd, merge } => {
                check_mul_eq(lhs, signature, rhs, lopd, ropd, merge, hc)
            }
            VdMirTermDerivationConstruction::AtomMulSwap => todo!(),
            VdMirTermDerivationConstruction::OneMulAtom => {
                check_one_mul_atom(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom => {
                check_nonone_literal_mul_atom(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::NonZeroLiteralAddAtom => {
                check_nonzero_literal_add_atom(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::NfAddZero => {
                check_nf_add_zero(lhs, signature, rhs, hc)
            }
        }
    }
}

fn check_reflection<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    match signature.separator() {
        VdMirBaseChainingSeparator::Iff => (),
        VdMirBaseChainingSeparator::Relation(separator) => match separator {
            VdMirBaseRelationSeparator::Comparison(separator) => match separator {
                VdMirBaseComparisonSeparator::Eq => (),
                VdMirBaseComparisonSeparator::Ne => panic!(),
                VdMirBaseComparisonSeparator::Lt => panic!(),
                VdMirBaseComparisonSeparator::Gt => panic!(),
                VdMirBaseComparisonSeparator::Le => todo!("should we allow this?"),
                VdMirBaseComparisonSeparator::Ge => todo!("should we allow this?"),
            },
            VdMirBaseRelationSeparator::Containment(_) => panic!(),
        },
    }
    assert!(vd_mir_expr_deep_eq(leader, follower, hc.expr_arena()))
}

/// derive `a <nc> b => term <nc> 0` from `a - b <nc> 0 => term <nc> 0` and `a - b => term`
fn check_num_comparison<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    lhs_minus_rhs: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::Iff);
    let (a, leader_signature, b) = hc.split_any_trivial_chaining_separated_list(leader);
    let (term, follower_signature, zero) = hc.split_any_trivial_chaining_separated_list(follower);
    assert_eq!(leader_signature.separator(), follower_signature.separator());
    let VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::Comparison(separator)) =
        leader_signature.separator()
    else {
        unreachable!()
    };
    assert!(hc.literal(zero).is_zero());
    ds!(let (lhs_minus_rhs_lhs => term1) = lhs_minus_rhs.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (a1 - b1) = lhs_minus_rhs_lhs, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

/// obtain `a + (b + c) = term` from `a + b + c = term`
fn check_add_interchange<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
    // let expr_arena = hc.expr_arena();
}
