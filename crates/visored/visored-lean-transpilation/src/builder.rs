use lean_hir_expr::{
    builder::LeanHirExprBuilder, expr::LnHirExprArena, stmt::LnHirStmtArena,
    tactic::LnHirTacticArena,
};
use salsa::Db;
use std::ops::{Deref, DerefMut};
use visored_hir_expr::{
    expr::VdHirExprArenaRef, region::VdHirExprRegionData, stmt::VdHirStmtArenaRef,
};

use crate::dictionary::VdLeanTranspilationDictionary;

pub struct VdLeanTranspilationBuilder<'a> {
    lean_hir_expr_builder: LeanHirExprBuilder<'a>,
    expr_arena: VdHirExprArenaRef<'a>,
    stmt_arena: VdHirStmtArenaRef<'a>,
    dictionary: &'a VdLeanTranspilationDictionary,
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub fn new0(
        db: &'db ::salsa::Db,
        vd_hir_expr_region_data: &'db VdHirExprRegionData,
        dictionary: &'db VdLeanTranspilationDictionary,
    ) -> Self {
        Self {
            lean_hir_expr_builder: LeanHirExprBuilder::new(db),
            expr_arena: vd_hir_expr_region_data.expr_arena(),
            stmt_arena: vd_hir_expr_region_data.stmt_arena(),
            dictionary,
        }
    }

    pub fn new(
        db: &'db ::salsa::Db,
        expr_arena: VdHirExprArenaRef<'db>,
        stmt_arena: VdHirStmtArenaRef<'db>,
        dictionary: &'db VdLeanTranspilationDictionary,
    ) -> Self {
        Self {
            lean_hir_expr_builder: LeanHirExprBuilder::new(db),
            expr_arena,
            stmt_arena,
            dictionary,
        }
    }
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub fn expr_arena(&self) -> VdHirExprArenaRef<'db> {
        self.expr_arena
    }

    pub fn stmt_arena(&self) -> VdHirStmtArenaRef<'db> {
        self.stmt_arena
    }

    pub fn dictionary(&self) -> &VdLeanTranspilationDictionary {
        self.dictionary
    }
}

impl<'db> Deref for VdLeanTranspilationBuilder<'db> {
    type Target = LeanHirExprBuilder<'db>;

    fn deref(&self) -> &Self::Target {
        &self.lean_hir_expr_builder
    }
}

impl<'db> DerefMut for VdLeanTranspilationBuilder<'db> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lean_hir_expr_builder
    }
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub fn finish(self) -> (LnHirExprArena, LnHirStmtArena, LnHirTacticArena) {
        self.lean_hir_expr_builder.finish()
    }
}
