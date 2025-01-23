pub mod finish;
pub mod neg;
pub mod pow;
pub mod product;
mod sqrt;
pub mod sub;
pub mod sum;

use self::{finish::*, neg::*, pow::*, product::*, sqrt::*, sub::*, sum::*};
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
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
};
use visored_term::term::literal::VdLiteral;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Reflection,
    NumComparison {
        lhs_nf: VdMirTermDerivationIdx,
        rhs_nf: VdMirTermDerivationIdx,
        lhs_nf_minus_rhs_nf_nf: VdMirTermDerivationIdx,
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
    /// derive `a + c => c + 1 * a` if `a` is an atom and `c` is a nonzero literal
    AtomAddNonZeroLiteral,
    /// derive `a + b => 0 + 1 * a + b` if `a` is an atom and `b` is a product with higher stem
    /// or derive `a + b => 0 + b + 1 * a` if `a` is an atom and `b` is a product with lower stem
    /// or derive `a + b => 0 + c * a` if `a` is an atom and `b` is a product with same stem and coefficient d=c-1 and `c` is nonzero
    /// or derive `a + b => 0` if `a` is an atom and `b` is a product with same stem and coefficient d=-1
    AtomAddProduct {
        comparison: core::cmp::Ordering,
    },
    /// derive `a + b * x + c * x => a + (b + c) * x`
    SumAddProductEqualKeep,
    /// derive `a + b * x + c * x => a` if `b + c` is zero
    SumAddProductEqualCancel,
    /// derive `a + b + c => term` from `a + c => term_ac` and `term_ac + b => term`
    SumAddProductGreater {
        a_add_c_nf: VdMirTermDerivationIdx,
    },
    LiteralMulLiteral,
    MulEq {
        lopd: VdMirTermDerivationIdx,
        ropd: VdMirTermDerivationIdx,
        merge: VdMirTermDerivationIdx,
    },
    AtomMulSwap,
    /// derive `1 * a => term` from `a => term`
    OneMul {
        a_nf: VdMirTermDerivationIdx,
    },
    /// derive `c * b => c * b^1` if `c` is a litnum
    NonOneLiteralMulAtom,
    /// derive `c + 0 => c`
    NfAddZero,
    NonTrivialFinish {
        src_nf: VdMirTermDerivationIdx,
        dst_nf: VdMirTermDerivationIdx,
    },
    AtomMulAtom {
        comparison: core::cmp::Ordering,
    },
    Sqrt {
        radicand_nf: VdMirTermDerivationIdx,
    },
    /// derive `(a * b) * c => term` from `a * b => lterm` and `lterm * c => term`
    MulAssoc {
        rsignature: VdBaseFoldingSeparatorSignature,
        merge_rlopd_nf: VdMirTermDerivationIdx,
        merge_rropd_nf: VdMirTermDerivationIdx,
    },
    NonReducedPower {
        base: VdMirTermDerivationIdx,
        exponent: VdMirTermDerivationIdx,
    },
    PowerOne {
        base: VdMirTermDerivationIdx,
    },
    /// derive `-a => term` from `(-1) * a => term`
    NegEqsMinusOneMul {
        minus_one_mul_a_nf: VdMirTermDerivationIdx,
    },
    /// derive `0 + a => term` from `a => term`
    ZeroAdd {
        a_nf: VdMirTermDerivationIdx,
    },
    /// derive `a + b => term` from `a + 1 * b => term` if `b` is an atom
    AddAtom {
        add_product_nf: VdMirTermDerivationIdx,
    },
    ProductAddProductLess,
    ProductAddProductEqualKeep,
    ProductAddProductEqualCancel,
    /// derive `a + b => 0 + b + a` if `a` and `b` are products and the stem of `a` is greater than the stem of `b`
    ProductAddProductGreater,
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
        match *self {
            VdMirTermDerivationConstruction::Reflection => check_reflection(prop, hc),
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => {
                check_literal_add_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::NumComparison {
                lhs_nf,
                rhs_nf,
                lhs_nf_minus_rhs_nf_nf,
            } => check_num_comparison(prop, lhs_nf, rhs_nf, lhs_nf_minus_rhs_nf_nf, hc),
            VdMirTermDerivationConstruction::SubEqsAddNeg { add_neg } => {
                check_sub_eqs_add_neg(prop, add_neg, hc)
            }
            VdMirTermDerivationConstruction::AdditionInterchange => check_add_interchange(prop, hc),
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
            VdMirTermDerivationConstruction::NegEqsMinusOneMul { minus_one_mul_a_nf } => {
                check_neg_eqs_minus_one_mul(prop, minus_one_mul_a_nf, hc)
            }
            VdMirTermDerivationConstruction::AddEq {
                lopd, ropd, merge, ..
            } => check_add_eq(prop, lopd, ropd, merge, hc),
            VdMirTermDerivationConstruction::AtomAddNonZeroLiteral => check_atom_add_swap(prop, hc),
            VdMirTermDerivationConstruction::LiteralMulLiteral => {
                check_literal_mul_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::MulEq { lopd, ropd, merge } => {
                check_mul_eq(prop, lopd, ropd, merge, hc)
            }
            VdMirTermDerivationConstruction::AtomMulSwap => todo!(),
            VdMirTermDerivationConstruction::OneMul { a_nf } => check_one_mul(prop, a_nf, hc),
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom => {
                check_nonone_literal_mul_atom(prop, hc)
            }
            VdMirTermDerivationConstruction::NfAddZero => check_nf_add_zero(prop, hc),
            VdMirTermDerivationConstruction::NonTrivialFinish { src_nf, dst_nf } => {
                check_non_trivial_finish(prop, src_nf, dst_nf, hc)
            }
            VdMirTermDerivationConstruction::AtomMulAtom { comparison } => {
                check_atom_mul_atom(prop, comparison, hc)
            }
            VdMirTermDerivationConstruction::Sqrt { radicand_nf } => {
                check_sqrt(prop, radicand_nf, hc)
            }
            VdMirTermDerivationConstruction::MulAssoc {
                rsignature,
                merge_rlopd_nf,
                merge_rropd_nf,
            } => check_mul_assoc(prop, rsignature, merge_rlopd_nf, merge_rropd_nf, hc),
            VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => {
                check_non_reduced_power(prop, base, exponent, hc)
            }
            VdMirTermDerivationConstruction::PowerOne { base } => check_power_one(prop, base, hc),
            VdMirTermDerivationConstruction::AtomAddProduct { comparison } => {
                check_atom_add_product(prop, comparison, hc)
            }
            VdMirTermDerivationConstruction::SumAddProductGreater { a_add_c_nf } => {
                check_sum_add_product_greater(prop, a_add_c_nf, hc)
            }
            VdMirTermDerivationConstruction::ZeroAdd { a_nf } => check_zero_add(prop, a_nf, hc),
            VdMirTermDerivationConstruction::AddAtom { add_product_nf } => {
                check_add_atom(prop, add_product_nf, hc)
            }
            VdMirTermDerivationConstruction::SumAddProductEqualKeep => todo!(),
            VdMirTermDerivationConstruction::SumAddProductEqualCancel => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductLess => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductEqualKeep => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductEqualCancel => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductGreater => {
                check_product_add_product_greater(prop, hc)
            }
        }
    }
}

fn check_reflection<'db, Src>(prop: VdMirExprIdx, hc: &mut VdMirHypothesisConstructor<'db, Src>) {
    let (lhs, signature, rhs) = hc.split_any_trivial_chaining_separated_list(prop);
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
    assert_deep_eq!(lhs, rhs, hc)
}

/// derive `a <nc> b => term <nc> 0` from `a - b <nc> 0 => term <nc> 0` and `a - b => term`
fn check_num_comparison<'db, Src>(
    prop: VdMirExprIdx,
    a_nf: VdMirTermDerivationIdx,
    b_nf: VdMirTermDerivationIdx,
    a_nf_minus_a_nf_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (leader => follower) = prop, hc);
    let (a, leader_signature, b) = hc.split_any_trivial_chaining_separated_list(leader);
    let (term, follower_signature, zero) = hc.split_any_trivial_chaining_separated_list(follower);
    assert_eq!(leader_signature.separator(), follower_signature.separator());
    let VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::Comparison(separator)) =
        leader_signature.separator()
    else {
        unreachable!()
    };
    assert!(hc.literal(zero).is_zero());
    ds!(let (a_nf_minus_b_nf => term1) = a_nf_minus_a_nf_nf.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (a1 => a_nf) = a_nf.prop(hc), hc);
    ds!(let (b1 => b_nf) = b_nf.prop(hc), hc);
    ds!(let (a_nf1 - b_nf1) = a_nf_minus_b_nf, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(a_nf1, a_nf, hc);
    assert_deep_eq!(b_nf1, b_nf, hc);
}

/// obtain `a + (b + c) = term` from `a + b + c = term`
fn check_add_interchange<'db, Src>(prop: VdMirExprIdx, hc: &VdMirHypothesisConstructor<'db, Src>) {
    todo!()
    // let expr_arena = hc.expr_arena();
}
