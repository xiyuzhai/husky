use super::{expr::VdBsqExpr, *};
use term::comnum::{
    atom::{VdBsqAtomTerm, VdBsqComnumAtomTermData},
    product::{VdBsqProductStem, VdBsqProductTerm},
    sum::VdBsqSumTerm,
    VdBsqComnumTerm,
};

// returns unit because we just cache the results
pub fn cache_trivial_boundsm<'db, 'sess>(term: VdBsqComnumTerm<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    VdBsqManeuverCall::CacheTrivialBounds.wrap(cache_trivial_boundsm_inner(term))
}

fn cache_trivial_boundsm_inner<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    #[unify_elabm]
    match term {
        VdBsqComnumTerm::Atom(atom) => cache_atom_trivial_boundsm(atom),
        VdBsqComnumTerm::Sum(sum) => cache_sum_trivial_boundsm(sum),
        VdBsqComnumTerm::Product(product) => cache_product_trivial_boundsm(product),
    }
}

fn cache_atom_trivial_boundsm<'db, 'sess>(atom: VdBsqAtomTerm<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    match atom.data() {
        VdBsqComnumAtomTermData::Variable {
            lx_math_letter,
            local_defn_idx,
            ty,
        } => (),
    }
}

fn cache_sum_trivial_boundsm<'db, 'sess>(sum: VdBsqSumTerm<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    ()
}

fn cache_product_trivial_boundsm<'db, 'sess>(
    product: VdBsqProductTerm<'sess>,
) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    match product.stem() {
        VdBsqProductStem::Atom(stem) => todo!(),
        VdBsqProductStem::NonTrivial(stem) => {
            if stem.exponentials().len() == 1 {
                let (base, exponent) = stem.exponentials().data()[0];
                base.expr(elr, hc).cache();
                match exponent {
                    term::num::VdBsqNumTerm::Litnum(vd_bsq_litnum_term) => todo!(),
                    term::num::VdBsqNumTerm::Comnum(vd_bsq_comnum_term) => todo!(),
                }
            }
        }
    }
}
