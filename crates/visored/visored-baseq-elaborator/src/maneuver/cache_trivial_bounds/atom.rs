use super::*;

pub(super) fn calc_atom_trivial_bounds<'db, 'sess>(
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
