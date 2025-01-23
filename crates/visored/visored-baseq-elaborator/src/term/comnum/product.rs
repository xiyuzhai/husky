use std::iter::once;

use super::*;
use either::*;
use smallvec::*;
use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};
use visored_signature::signature::sqrt::{VdBaseSqrtSignature, VdSqrtSignature};

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct VdBsqProductTerm<'sess> {
    litnum_factor: VdBsqLitnumTerm<'sess>,
    stem: VdBsqProductStem<'sess>,
}

impl<'sess> VdBsqProductTerm<'sess> {
    pub fn new(
        litnum_factor: impl Into<VdBsqLitnumTerm<'sess>>,
        stem: impl Into<VdBsqProductStem<'sess>>,
    ) -> VdBsqNumTerm<'sess> {
        let litnum_factor = litnum_factor.into();
        let stem = stem.into();
        match litnum_factor {
            VdBsqLitnumTerm::ZERO => 0.into(),
            VdBsqLitnumTerm::ONE => match stem {
                VdBsqProductStem::Atom(stem) => stem.into(),
                VdBsqProductStem::NonTrivial(_) => Self {
                    litnum_factor,
                    stem,
                }
                .into(),
            },
            _ => Self {
                litnum_factor,
                stem,
            }
            .into(),
        }
    }

    pub fn new2(
        litnum_factor: VdBsqLitnumTerm<'sess>,
        exponentials: VdBsqExponentialPowers<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        let base = match VdBsqProductStem::new(exponentials, db) {
            Left(base) => base,
            Right(term) => return term.mul_litnum(litnum_factor, db),
        };
        Self::new(litnum_factor, base)
    }

    pub fn with_litnum_factor(self, litnum_factor: VdBsqLitnumTerm<'sess>) -> VdBsqNumTerm<'sess> {
        Self::new(litnum_factor, self.stem)
    }

    pub fn with_litnum_factor_update(
        self,
        f: impl FnOnce(VdBsqLitnumTerm<'sess>) -> VdBsqLitnumTerm<'sess>,
    ) -> VdBsqNumTerm<'sess> {
        Self::new(f(self.litnum_factor), self.stem)
    }
}

impl<'sess> VdBsqProductTerm<'sess> {
    pub fn litnum_factor(self) -> VdBsqLitnumTerm<'sess> {
        self.litnum_factor
    }

    pub fn stem(&self) -> VdBsqProductStem<'sess> {
        self.stem
    }
}

impl<'sess> VdBsqProductTerm<'sess> {
    pub fn mul_litnum(
        self,
        litnum: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        Self::new(self.litnum_factor.mul(litnum, db), self.stem)
    }
}

impl<'sess> From<VdBsqProductStem<'sess>> for VdBsqComnumTerm<'sess> {
    fn from(base: VdBsqProductStem<'sess>) -> Self {
        match VdBsqProductTerm::new(VdBsqLitnumTerm::ONE, base) {
            VdBsqNumTerm::Comnum(comnum) => comnum,
            _ => unreachable!(),
        }
    }
}

impl<'sess> VdBsqProductTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let Self {
            litnum_factor: factor,
            stem: base,
        } = self;
        debug_assert!(!factor.is_zero());
        if factor.is_one() {
            base.show_fmt(precedence_range, f)
        } else {
            if precedence_range.contains(VdPrecedence::MUL_DIV) {
                self.show_fmt_inner(f)
            } else {
                f.write_str("(")?;
                self.show_fmt_inner(f)?;
                f.write_str(")")
            }
        }
    }

    fn show_fmt_inner(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.litnum_factor
            .show_fmt(VdPrecedenceRange::MUL_DIV_LEFT, f)?;
        match self.stem {
            VdBsqProductStem::Atom(_) => (),
            VdBsqProductStem::NonTrivial(vd_bsq_non_trivial_product_base) => f.write_str(" × ")?,
        }
        self.stem.show_fmt(VdPrecedenceRange::MUL_DIV_RIGHT, f)
    }
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqProductStem<'sess> {
    Atom(VdBsqAtomTerm<'sess>),
    NonTrivial(VdBsqNonTrivialProductStem<'sess>),
}

#[floated]
pub struct VdBsqNonTrivialProductStem<'sess> {
    #[return_ref]
    exponentials: VdBsqExponentialPowers<'sess>,
}

impl<'sess> VdBsqNonTrivialProductStem<'sess> {
    pub fn outer_precedence(&self) -> VdPrecedence {
        let exponentials = self.exponentials();
        if exponentials.len() == 1 {
            let (base, exponent) = exponentials.data()[0];
            if exponent.is_one_trivially() {
                let base_outer_precedence = base.outer_precedence();
                if VdPrecedenceRange::MUL_DIV_LEFT.contains(base_outer_precedence) {
                    base_outer_precedence
                } else {
                    VdPrecedence::ATOM
                }
            } else {
                VdPrecedence::MUL_DIV
            }
        } else {
            VdPrecedence::MUL_DIV
        }
    }
}

impl<'sess> std::fmt::Debug for VdBsqNonTrivialProductStem<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdBsqNonTrivialProductStem(`")?;
        self.show_fmt(VdPrecedenceRange::ANY, f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdBsqProductStem<'sess> {
    #[track_caller]
    pub fn new(
        exponentials: VdBsqExponentialPowers<'sess>,
        db: &'sess FloaterDb,
    ) -> Either<Self, VdBsqNumTerm<'sess>> {
        if exponentials.len() == 1 {
            let (base, exponent) = exponentials.data()[0];
            match exponent {
                VdBsqNumTerm::ZERO => todo!(),
                VdBsqNumTerm::ONE => match base {
                    VdBsqNumTerm::Litnum(vd_bsq_litnum_term) => todo!(),
                    VdBsqNumTerm::Comnum(comnum) => match comnum {
                        VdBsqComnumTerm::Atom(atom) => return Left(atom.into()),
                        VdBsqComnumTerm::Sum(sum) => return Right(sum.into()),
                        VdBsqComnumTerm::Product(product) => return Right(product.into()),
                    },
                },
                _ => (),
            }
        }
        Left(VdBsqNonTrivialProductStem::new_guaranteed(exponentials, db).into())
    }

    pub fn from_parts(
        exponentials: VdBsqExponentialParts<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        let mut builder = VdBsqProductBuilder::new(db);
        for (base, exponent) in exponentials {
            builder.mul_exponential(base, exponent);
        }
        builder.finish()
    }

    pub fn new_power(
        base: VdBsqNumTerm<'sess>,
        exponent: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Either<Self, VdBsqNumTerm<'sess>> {
        let exponentials = [(base, exponent)].into_iter().collect();
        Self::new(exponentials, db)
    }
}

impl<'sess> VdBsqNonTrivialProductStem<'sess> {
    #[track_caller]
    pub fn new_guaranteed(
        exponentials: VdBsqExponentialPowers<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        #[cfg(debug_assertions)]
        {
            debug_assert!(exponentials.len() > 0);
            if exponentials.len() == 1 {
                let (base, exponent) = exponentials.data()[0];
                debug_assert!(!exponent.is_zero_trivially());
                if exponent.is_one_trivially() {
                    match base {
                        VdBsqNumTerm::Litnum(_) => unreachable!(),
                        VdBsqNumTerm::Comnum(_) => unreachable!(),
                    }
                }
            }
            for &(base, exponent) in &exponentials {
                debug_assert!(!exponent.is_zero_trivially());
            }
        }
        Self::new_inner(exponentials, db)
    }
}

impl<'sess> VdBsqComnumTerm<'sess> {
    pub fn new_power(
        base: VdBsqNumTerm<'sess>,
        exponent: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        match VdBsqProductStem::new_power(base, exponent, db) {
            Left(base) => base.into(),
            Right(_) => todo!(),
        }
    }
}

impl<'sess> VdBsqNumTerm<'sess> {
    pub fn new_product(
        litn_coefficient: VdBsqLitnumTerm<'sess>,
        exponentials: VdBsqExponentialPowers<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqProductTerm::new2(litn_coefficient, exponentials, db)
    }

    pub fn new_power(
        base: VdBsqNumTerm<'sess>,
        exponent: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqComnumTerm::new_power(base, exponent, db).into()
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn new_power(
        base: impl Into<VdBsqNumTerm<'sess>>,
        exponent: impl Into<VdBsqNumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqNumTerm::new_power(base.into(), exponent.into(), db).into()
    }
}

impl<'sess> VdBsqProductStem<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqProductStem::Atom(slf) => slf.show_fmt(precedence_range, f),
            VdBsqProductStem::NonTrivial(slf) => slf.show_fmt(precedence_range, f),
        }
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdBsqProductStem::Atom(term) => term.outer_precedence(),
            VdBsqProductStem::NonTrivial(term) => term.outer_precedence(),
        }
    }
}

impl<'sess> VdBsqNonTrivialProductStem<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let outer_precedence = self.outer_precedence();
        if precedence_range.contains(outer_precedence) {
            self.show_fmt_inner(f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(f)?;
            f.write_str(")")
        }
    }

    fn show_fmt_inner(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &(base, exponent) in self.exponentials() {
            match exponent {
                VdBsqNumTerm::ZERO => unreachable!(),
                VdBsqNumTerm::ONE => base.show_fmt(VdPrecedenceRange::MUL_DIV_LEFT, f)?,
                _ => {
                    base.show_fmt(VdPrecedenceRange::ATOM, f)?;
                    f.write_str("^")?;
                    exponent.show_fmt(VdPrecedenceRange::ATOM, f)?;
                    f.write_str("")?
                }
            }
        }
        Ok(())
    }
}

impl<'db, 'sess> VdBsqProductTerm<'sess> {
    pub fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        product_expr(self.stem(), self.litnum_factor(), elr, hc)
    }
}

impl<'db, 'sess> VdBsqProductStem<'sess> {
    pub fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        match self {
            VdBsqProductStem::Atom(slf) => elr.mk_pow(slf.expr(elr, hc), elr.mk_i128(1), hc),
            VdBsqProductStem::NonTrivial(slf) => slf.expr(elr, hc),
        }
    }
}

impl<'db, 'sess> VdBsqNonTrivialProductStem<'sess> {
    pub fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        if self.exponentials().len() == 1 {
            return exponential_expr(self.exponentials().data()[0], elr, hc);
        }
        let mut exponentials = self.exponentials().into_iter().copied();
        let leader = exponential_expr(exponentials.next().unwrap(), elr, hc);
        let mut prev_exponential_ty = leader.ty();
        let mut followers = smallvec![];
        for exponential in exponentials {
            let exponential = exponential_expr(exponential, elr, hc);
            let signature = hc.infer_mul_signature(prev_exponential_ty, exponential.ty());
            followers.push((signature, exponential));
            prev_exponential_ty = signature.expr_ty();
        }
        elr.mk_expr(
            VdBsqExprData::FoldingSeparatedList { leader, followers },
            prev_exponential_ty,
        )
    }
}

fn product_expr<'db, 'sess>(
    stem: VdBsqProductStem<'sess>,
    factor: VdBsqLitnumTerm<'sess>,
    elr: &VdBsqElaboratorInner<'db, 'sess>,
    hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExpr<'sess> {
    assert!(!factor.is_zero());
    elr.mk_mul(factor.expr(elr, hc), stem.expr(elr, hc), hc)
}

fn exponential_expr<'db, 'sess>(
    (base, exponent): (VdBsqNumTerm<'sess>, VdBsqNumTerm<'sess>),
    elr: &VdBsqElaboratorInner<'db, 'sess>,
    hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExpr<'sess> {
    assert!(!exponent.is_zero_trivially());
    let base = base.expr(elr, hc);
    let exponent = exponent.expr(elr, hc);
    let power_signature = hc.infer_power_signature(base.ty(), exponent.ty());
    let arguments = smallvec![base, exponent];
    elr.mk_expr(
        VdBsqExprData::Application {
            function: VdMirFunc::Power(power_signature),
            arguments,
        },
        power_signature.expr_ty(),
    )
}
