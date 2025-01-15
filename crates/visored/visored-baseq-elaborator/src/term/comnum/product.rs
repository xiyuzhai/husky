use super::*;
use either::*;
use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};

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

impl<'sess> From<VdBsqProductStem<'sess>> for VdBsqProductTerm<'sess> {
    fn from(base: VdBsqProductStem<'sess>) -> Self {
        Self {
            litnum_factor: VdBsqLitnumTerm::ONE,
            stem: base,
        }
    }
}

impl<'sess> From<VdBsqProductStem<'sess>> for VdBsqComnumTerm<'sess> {
    fn from(base: VdBsqProductStem<'sess>) -> Self {
        Self::Product(base.into())
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
        f.debug_struct("VdBsqNonTrivialProductBase")
            .field("exponentials", self.exponentials())
            .finish()
    }
}

impl<'sess> VdBsqProductStem<'sess> {
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
        VdBsqNumTerm::Comnum(VdBsqComnumTerm::new_power(base, exponent, db))
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn new_power(
        base: impl Into<VdBsqNumTerm<'sess>>,
        exponent: impl Into<VdBsqNumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqTerm::Comnum(VdBsqComnumTerm::new_power(base.into(), exponent.into(), db))
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
