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
}
