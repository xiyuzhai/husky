use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_neg_term_derivation_construction(
        &mut self,
        opd: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let opd = self.transcribe_expr_term_derivation(opd, hc);
        match *opd.data() {
            VdBsqExprData::Literal(vd_literal) => VdMirTermDerivationConstruction::NegLiteral,
            VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
            VdBsqExprData::Application {
                function,
                ref arguments,
            } => todo!(),
            VdBsqExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => todo!(),
            VdBsqExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => todo!(),
            VdBsqExprData::ItemPath(vd_item_path) => todo!(),
        }
    }
}
