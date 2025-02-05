use super::{expr::VdBsqExpr, *};
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
            cache_trivial_boundsm_inner(term, elr);
            f(elr, ())
        },
    )
}

fn cache_trivial_boundsm_inner<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) {
    let bounds = match term {
        VdBsqComnumTerm::Atom(atom) => calc_atom_trivial_bounds(atom, elr),
        VdBsqComnumTerm::Sum(sum) => calc_sum_trivial_bounds(sum, elr),
        VdBsqComnumTerm::Product(product) => calc_product_trivial_bounds(product, elr),
    };
    todo!()
}

fn calc_atom_trivial_bounds<'db, 'sess>(
    atom: VdBsqAtomTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Option<Vec<VdBsqHypothesisIdx<'sess>>> {
    match atom.data() {
        VdBsqComnumAtomTermData::Variable {
            lx_math_letter,
            local_defn_idx,
            ty,
        } => None,
    }
}

fn calc_sum_trivial_bounds<'db, 'sess>(
    sum: VdBsqSumTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Option<Vec<VdBsqHypothesisIdx<'sess>>> {
    None
}

fn calc_product_trivial_bounds<'db, 'sess>(
    product: VdBsqProductTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Option<Vec<VdBsqHypothesisIdx<'sess>>> {
    let mut bounds = vec![];
    bounds.extend(try_even_power(product, elr));
    Some(bounds)
}

fn try_even_power<'db, 'sess>(
    product: VdBsqProductTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Option<VdBsqHypothesisIdx<'sess>> {
    match product.stem() {
        VdBsqProductStem::Atom(stem) => todo!(),
        VdBsqProductStem::NonTrivial(stem) => {
            if stem.exponentials().len() == 1 {
                let (base, exponent) = stem.exponentials().data()[0];
                match exponent {
                    VdBsqNumTerm::Litnum(VdBsqLitnumTerm::Int128(i)) if i % 2 == 0 => (),
                    _ => return None,
                }
                match base.ty(elr) {
                    VdPreludeSetPath::NaturalNumber
                    | VdPreludeSetPath::RationalNumber
                    | VdPreludeSetPath::Integer
                    | VdPreludeSetPath::RealNumber => {
                        let hypothesis = todo!();
                        Some(hypothesis)
                    }
                    VdPreludeSetPath::ComplexNumber => return None,
                    _ => todo!(),
                }
            } else {
                None
            }
        }
    }
}
