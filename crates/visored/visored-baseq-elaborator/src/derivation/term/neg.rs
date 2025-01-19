use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_neg_term_derivation_construction(
        &mut self,
        opd: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let opd = self.transcribe_expr_term_derivation(opd, hc);
        match *opd.data() {
            VdBsqExprFldData::Literal(vd_literal) => VdMirTermDerivationConstruction::NegLiteral,
            VdBsqExprFldData::Variable(lx_math_letter, arena_idx) => todo!(),
            VdBsqExprFldData::Application {
                function,
                ref arguments,
            } => todo!(),
            VdBsqExprFldData::FoldingSeparatedList {
                leader,
                ref followers,
            } => todo!(),
            VdBsqExprFldData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => todo!(),
            VdBsqExprFldData::ItemPath(vd_item_path) => todo!(),
        }
    }
}
