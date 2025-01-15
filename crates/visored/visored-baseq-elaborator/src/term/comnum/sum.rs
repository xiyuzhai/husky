use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};

use super::*;

#[floated]
pub struct VdBsqSumTerm<'sess> {
    #[return_ref]
    data: VdBsqComnumSumTermData<'sess>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct VdBsqComnumSumTermData<'sess> {
    constant_term: VdBsqLitnumTerm<'sess>,
    monomials: VdBsqMonomialCoefficients<'sess>,
}

impl<'sess> From<VdBsqSumTerm<'sess>> for VdBsqNumTerm<'sess> {
    fn from(value: VdBsqSumTerm<'sess>) -> Self {
        VdBsqNumTerm::Comnum(VdBsqComnumTerm::Sum(value))
    }
}

impl<'sess> VdBsqSumTerm<'sess> {
    pub fn new(
        constant_term: impl Into<VdBsqLitnumTerm<'sess>>,
        monomials: VdBsqMonomialCoefficients<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        let constant_term = constant_term.into();
        #[cfg(debug_assertions)]
        {
            for (monomial, coeff) in monomials.data() {
                debug_assert!(coeff.is_nonzero(), "monomial coefficient should be nonzero");
            }
            debug_assert!(
                !(constant_term.is_zero() && monomials.len() == 1),
                "should be reduced to product"
            );
        }
        Self::new_inner(
            VdBsqComnumSumTermData {
                constant_term,
                monomials,
            },
            db,
        )
    }
}

impl<'sess> VdBsqSumTerm<'sess> {
    pub fn constant_term(self) -> VdBsqLitnumTerm<'sess> {
        self.data().constant_term()
    }

    pub fn nonzero_constant_term(self) -> Option<VdBsqLitnumTerm<'sess>> {
        if self.constant_term().is_zero() {
            None
        } else {
            Some(self.constant_term())
        }
    }

    pub fn monomials(self) -> &'sess VdBsqMonomialCoefficients<'sess> {
        self.data().monomials()
    }
}

impl<'sess> VdBsqComnumSumTermData<'sess> {
    pub fn constant_term(&self) -> VdBsqLitnumTerm<'sess> {
        self.constant_term
    }

    pub fn monomials(&self) -> &VdBsqMonomialCoefficients<'sess> {
        &self.monomials
    }
}

impl<'sess> std::fmt::Debug for VdBsqSumTerm<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // self.show_fmt(VdPrecedenceRange::ANY, f)
        f.debug_struct("VdBsqSumComnumTerm")
            .field("constant_term", &self.constant_term())
            .field("monomials", &self.monomials())
            .finish()
    }
}

impl<'sess> VdBsqSumTerm<'sess> {
    pub fn show_fmt(
        &self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.data().show_fmt(precedence_range, f)
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        self.data().outer_precedence()
    }
}

impl<'sess> VdBsqComnumSumTermData<'sess> {
    pub fn show_fmt(
        &self,
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

    pub fn outer_precedence(&self) -> VdPrecedence {
        let num_of_summands = if self.constant_term.is_zero() {
            self.monomials.len()
        } else {
            self.monomials.len() + 1
        };
        if num_of_summands == 1 {
            let (monomial, coeff) = self.monomials.data()[0];
            match coeff {
                VdBsqLitnumTerm::ONE => monomial.outer_precedence(),
                _ => VdPrecedence::MUL_DIV,
            }
        } else {
            VdPrecedence::REDUCE_PREFIX
        }
    }

    fn show_fmt_inner(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.constant_term.is_zero() {
            self.constant_term
                .show_fmt(VdPrecedenceRange::ADD_SUB_LEFT, f)?;
            f.write_str(" + ")?;
        }
        for (i, (monomial, coefficient)) in self.monomials.iter().enumerate() {
            if i > 0 {
                f.write_str(" + ")?;
            }
            if !coefficient.is_one() {
                coefficient.show_fmt(VdPrecedenceRange::MUL_DIV_RIGHT, f)?;
                match monomial {
                    VdBsqProductStem::Atom(term) => (),
                    VdBsqProductStem::NonTrivial(base) => match base.exponentials().data()[0].0 {
                        VdBsqNumTerm::Litnum(_) => f.write_str(" × ")?,
                        VdBsqNumTerm::Comnum(_) => (),
                    },
                }
            }
            monomial.show_fmt(VdPrecedenceRange::MUL_DIV_RIGHT, f)?;
        }
        Ok(())
    }
}

impl<'sess> VdBsqSumTerm<'sess> {
    pub fn neg(self, db: &'sess FloaterDb) -> VdBsqSumTerm<'sess> {
        todo!()
    }

    pub fn mul128(self, rhs: i128, db: &'sess FloaterDb) -> VdBsqNumTerm<'sess> {
        todo!()
    }

    pub fn mul_litnum(
        self,
        litnum: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        if litnum.is_zero() {
            return VdBsqNumTerm::ZERO;
        }
        if litnum.is_one() {
            return self.into();
        }
        Self::new(
            self.constant_term().mul(litnum, db),
            self.monomials()
                .iter()
                .map(|&(monomial, coeff)| (monomial, coeff.mul(litnum, db)))
                .collect(),
            db,
        )
        .into()
    }

    pub fn div_litnum(
        self,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqComnumTerm<'sess>> {
        todo!()
    }
}
