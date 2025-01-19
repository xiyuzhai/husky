pub mod atom;
pub mod helpers;
pub mod product;
pub mod sum;

use self::{atom::*, product::*, sum::*};
use super::*;
use smallvec::*;
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;
use visored_opr::precedence::VdPrecedence;

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqComnumTerm<'sess> {
    Atom(VdBsqAtomTerm<'sess>),
    Sum(VdBsqSumTerm<'sess>),
    Product(VdBsqProductTerm<'sess>),
}

impl<'sess> VdBsqComnumTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqComnumTerm::Atom(term) => term.show_fmt(precedence_range, f),
            VdBsqComnumTerm::Sum(term) => term.show_fmt(precedence_range, f),
            VdBsqComnumTerm::Product(term) => term.show_fmt(precedence_range, f),
        }
    }
}

pub type VdBsqNonSumComnumTerms<'sess> = SmallVec<[VdBsqProductStem<'sess>; 4]>;
pub type VdBsqNonProductNumTermMap<'sess, T> = OrderedSmallVecPairMap<VdBsqNumTerm<'sess>, T, 4>;
pub type VdBsqNonSumComnumTermMap<'sess, T> = OrderedSmallVecPairMap<VdBsqProductStem<'sess>, T, 4>;
pub type VdBsqMonomialCoefficients<'sess> = VdBsqNonSumComnumTermMap<'sess, VdBsqLitnumTerm<'sess>>;
pub type VdBsqExponentialPowers<'sess> = VdBsqNonProductNumTermMap<'sess, VdBsqNumTerm<'sess>>;
pub type VdBsqExponentialPowersRef<'a, 'sess> = &'a [(VdBsqNumTerm<'sess>, VdBsqNumTerm<'sess>)];
pub type VdBsqExponentialParts<'sess> = Vec<(VdBsqNumTerm<'sess>, VdBsqNumTerm<'sess>)>;

impl<'sess> VdBsqComnumTerm<'sess> {
    pub fn neg(self, db: &'sess FloaterDb) -> VdBsqNumTerm<'sess> {
        match self {
            VdBsqComnumTerm::Atom(term) => term.neg(db).into(),
            VdBsqComnumTerm::Sum(term) => term.neg(db).into(),
            VdBsqComnumTerm::Product(product) => {
                product.with_litnum_factor_update(|litnum| litnum.neg(db))
            }
        }
    }

    pub fn mul128(self, rhs: i128, db: &'sess FloaterDb) -> VdBsqNumTerm<'sess> {
        if rhs == 0 {
            return VdBsqNumTerm::ZERO;
        }
        if rhs == 1 {
            return self.into();
        }
        match self {
            VdBsqComnumTerm::Atom(term) => term.mul_litnum(rhs, db),
            VdBsqComnumTerm::Sum(term) => term.mul128(rhs, db),
            VdBsqComnumTerm::Product(product) => product
                .with_litnum_factor_update(|litnum| litnum.mul128(rhs, db))
                .into(),
        }
    }

    pub fn mul_litnum(
        self,
        litnum: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        match self {
            VdBsqComnumTerm::Atom(term) => term.mul_litnum(litnum, db).into(),
            VdBsqComnumTerm::Sum(term) => term.mul_litnum(litnum, db).into(),
            VdBsqComnumTerm::Product(term) => term.mul_litnum(litnum, db).into(),
        }
    }

    pub fn div_litnum(
        self,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqNumTerm<'sess>> {
        if rhs.is_zero() {
            return None;
        }
        if rhs.is_one() {
            return Some(self.into());
        }
        match self {
            VdBsqComnumTerm::Atom(slf) => Some(slf.div_litnum(rhs, db).unwrap().into()),
            VdBsqComnumTerm::Sum(slf) => Some(slf.div_litnum(rhs, db).unwrap().into()),
            VdBsqComnumTerm::Product(product) => {
                Some(product.with_litnum_factor_update(|litnum| litnum.div(rhs, db).unwrap()))
            }
        }
    }
}

impl<'db, 'sess> VdBsqComnumTerm<'sess> {
    pub(crate) fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        match self {
            VdBsqComnumTerm::Atom(slf) => slf.expr(elr, hc),
            VdBsqComnumTerm::Sum(slf) => slf.expr(elr, hc),
            VdBsqComnumTerm::Product(slf) => slf.expr(elr, hc),
        }
    }
}
