use super::{expr::VdBsqExpr, *};
use hypothesis::{
    caches::trivial_bounds::VdBsqTrivialBoundsHypothesisCache,
    construction::{
        trivial_bound::VdBsqTrivialBoundHypothesisConstruction, VdBsqHypothesisConstruction,
    },
};
use num_bigint::Sign;
use term::{
    comnum::{
        atom::{VdBsqAtomTerm, VdBsqComnumAtomTermData},
        product::{VdBsqProductStem, VdBsqProductTerm},
        sum::VdBsqSumTerm,
        VdBsqComnumTerm,
    },
    litnum::VdBsqLitnumTerm,
    num::VdBsqNumTerm,
};
use visored_entity_path::path::set::VdPreludeSetPath;

// returns unit because we just cache the results
pub fn cache_trivial_boundsm<'db, 'sess>(term: VdBsqComnumTerm<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    VdBsqManeuverCall::CacheTrivialBounds.wrap(
        move |elr: &mut Elr<'db, 'sess>, f: &Heuristic<'_, 'db, 'sess, ()>| -> Mhr<'sess> {
            cache_trivial_bounds(term, elr);
            f(elr, ())
        },
    )
}

fn cache_trivial_bounds<'db, 'sess>(term: VdBsqComnumTerm<'sess>, elr: &mut Elr<'db, 'sess>) {
    VdBsqTrivialBoundsHypothesisCache::cache_trivial_bounds(
        term,
        |elr| calc_trivial_bounds(term, elr),
        elr,
    )
}

fn calc_trivial_bounds<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    match term {
        VdBsqComnumTerm::Atom(atom) => calc_atom_trivial_bounds(atom, elr),
        VdBsqComnumTerm::Sum(sum) => calc_sum_trivial_bounds(sum, elr),
        VdBsqComnumTerm::Product(product) => calc_product_trivial_bounds(product, elr),
    }
}

fn calc_atom_trivial_bounds<'db, 'sess>(
    atom: VdBsqAtomTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    match atom.data() {
        VdBsqComnumAtomTermData::Variable {
            lx_math_letter,
            local_defn_idx,
            ty,
        } => vec![],
    }
}

fn calc_sum_trivial_bounds<'db, 'sess>(
    sum: VdBsqSumTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    vec![]
}

fn calc_product_trivial_bounds<'db, 'sess>(
    product: VdBsqProductTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    let mut bounds = vec![];
    bounds.extend(try_even_power(product, elr));
    bounds
}

fn try_even_power<'db, 'sess>(
    product: VdBsqProductTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    match product.stem() {
        VdBsqProductStem::Atom(stem) => todo!(),
        VdBsqProductStem::NonTrivial(stem) => {
            if stem.exponentials().len() == 1 {
                let (base, exponent) = stem.exponentials().data()[0];
                match exponent {
                    VdBsqNumTerm::Litnum(VdBsqLitnumTerm::Int128(i)) if i % 2 == 0 => (),
                    _ => return vec![],
                }
                match base.ty(elr) {
                    VdPreludeSetPath::NaturalNumber
                    | VdPreludeSetPath::RationalNumber
                    | VdPreludeSetPath::Integer
                    | VdPreludeSetPath::RealNumber => {
                        let sign = product.litnum_factor().sign();
                        let prop = match sign {
                            Sign::Minus => {
                                let product = product.expr(elr);
                                elr.mk_lt(product, elr.mk_zero())
                            }
                            Sign::NoSign => unreachable!(),
                            Sign::Plus => {
                                let product = product.expr(elr);
                                elr.mk_lt(product, elr.mk_zero())
                            }
                        };
                        let construction = VdBsqHypothesisConstruction::TrivialBound(
                            VdBsqTrivialBoundHypothesisConstruction::EvenPower { sign },
                        );
                        let hypothesis = elr.hc.construct_new_hypothesis(prop, construction);
                        vec![hypothesis]
                    }
                    VdPreludeSetPath::ComplexNumber => vec![],
                    _ => todo!(),
                }
            } else {
                vec![]
            }
        }
    }
}
