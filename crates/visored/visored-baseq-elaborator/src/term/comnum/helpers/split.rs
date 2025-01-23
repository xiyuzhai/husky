use super::*;

impl<'sess> VdBsqSumTerm<'sess> {
    /// `f` takes in the inverse of the leading coefficient and returns the factor.
    ///
    /// Split into `factor * (normalized_constant_term + normalized_monomials)`.
    ///
    /// Returns `(factor, (normalized_constant_term, normalized_monomials))`
    pub fn split_fld(
        self,
        f: impl FnOnce(VdBsqLitnumTerm<'sess>) -> VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> (
        VdBsqLitnumTerm<'sess>,
        (VdBsqLitnumTerm<'sess>, VdBsqComnumTerm<'sess>),
    ) {
        let (factor, (litnum, monomials)) = self.split(f, db);
        let monomials = if monomials.len() > 1 {
            VdBsqSumTerm::new(0, monomials, db).into()
        } else {
            let (monomial, coeff) = monomials.data()[0];
            match coeff.mul_product_base(monomial, db) {
                VdBsqNumTerm::Litnum(_) => unreachable!("the split of a sum is always nontrivial"),
                VdBsqNumTerm::Comnum(comnum) => comnum,
            }
        };
        (factor, (litnum, monomials))
    }

    /// `f` takes in the inverse of the leading coefficient and returns the factor.
    ///
    /// Split into `factor * (normalized_constant_term + normalized_monomials)`.
    ///
    /// Returns `(factor, (normalized_constant_term, normalized_monomials))`
    pub fn split(
        self,
        f: impl FnOnce(VdBsqLitnumTerm<'sess>) -> VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> (
        VdBsqLitnumTerm<'sess>,
        (VdBsqLitnumTerm<'sess>, VdBsqMonomialCoefficients<'sess>),
    ) {
        let mut monomials = self.monomials().clone();
        debug_assert!(monomials.len() > 0);
        let coeff0 = monomials.data()[0].1;
        debug_assert!(coeff0.is_nonzero());
        let factor = f(coeff0);
        let inv_factor = factor.inv(db).expect("nonzero");
        let normalized_constant_term = self.constant_term().mul(inv_factor, db);
        let normalized_monomials = monomials.map_collect(|coeff| coeff.mul(inv_factor, db));
        (factor, (normalized_constant_term, normalized_monomials))
    }
}

/// `f` takes in the inverse of the leading coefficient and returns the factor.
///
/// Split into `factor * (normalized_constant_term + normalized_monomials)`.
///
/// Returns `(factor, (normalized_constant_term, normalized_monomials))`
impl<'sess> VdBsqComnumTerm<'sess> {
    pub fn split_sum_fld(
        self,
        f: impl FnOnce(VdBsqLitnumTerm<'sess>) -> VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> (
        VdBsqLitnumTerm<'sess>,
        (VdBsqLitnumTerm<'sess>, VdBsqComnumTerm<'sess>),
    ) {
        match self {
            VdBsqComnumTerm::Sum(sum) => sum.split_fld(f, db),
            VdBsqComnumTerm::Atom(_) => {
                let factor = f(1.into());
                let VdBsqNumTerm::Comnum(term) = self.div_litnum(factor, db).unwrap() else {
                    unreachable!()
                };
                (factor, (0.into(), term))
            }
            VdBsqComnumTerm::Product(product) => {
                let factor0 = product.litnum_factor();
                let factor = f(factor0);
                let VdBsqNumTerm::Comnum(term) =
                    product.with_litnum_factor(factor0.div(factor, db).unwrap())
                else {
                    unreachable!()
                };
                (factor, (0.into(), term))
            }
        }
    }
}
