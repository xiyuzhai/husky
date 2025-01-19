use visored_mir_opr::separator::{
    chaining::VdMirBaseChainingSeparator, folding::VdMirBaseFoldingSeparator,
};

use super::*;

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn mk_expr(&mut self, entry: VdMirExprEntry) -> VdMirExprIdx {
        self.expr_arena.alloc_one(entry)
    }

    pub fn mk_zero(&mut self, expected_ty: Option<VdType>) -> VdMirExprIdx {
        let db = self.db;
        self.expr_arena.alloc_one(VdMirExprEntry::new(
            VdMirExprData::Literal(VdLiteral::new_int128(0, db)),
            self.ty_menu.nat,
            expected_ty,
        ))
    }

    pub fn mk_exprs(
        &mut self,
        exprs: impl IntoIterator<Item = VdMirExprEntry>,
    ) -> VdMirExprIdxRange {
        self.expr_arena.alloc_many(exprs)
    }

    pub fn mk_sub(
        &mut self,
        lhs: VdMirExprIdx,
        rhs: VdMirExprIdx,
        expected_ty: Option<VdType>,
    ) -> VdMirExprIdx {
        todo!()
    }

    #[track_caller]
    pub fn split_folding_separated_list(
        &mut self,
        lhs: VdMirExprIdx,
        separator: VdMirBaseFoldingSeparator,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        match *self.expr_arena[lhs].data() {
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                for (signature, _) in followers {
                    assert_eq!(separator, signature.separator());
                }
                match followers.len() {
                    0 => unreachable!(),
                    1 => (leader, followers[0].1),
                    _ => todo!(),
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn split_trivial_chaining_separated_list(
        &mut self,
        lhs: VdMirExprIdx,
        separator: VdMirBaseChainingSeparator,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        match *self.expr_arena[lhs].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: None,
            } => {
                for (signature, _) in followers {
                    assert_eq!(separator, signature.separator());
                }
                match followers.len() {
                    0 => unreachable!(),
                    1 => (leader, followers[0].1),
                    _ => todo!(),
                }
            }
            _ => unreachable!(),
        }
    }
}
