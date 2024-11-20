use lean_coword::ident::LnIdent;
use lean_mir_expr::{
    builder::{LnMirExprBuilder, WithLnNamespace},
    expr::{LnMirExprArena, LnMirExprData},
    item_defn::{def::LnMirDefBody, LnItemDefnArena, LnItemDefnData, LnItemDefnIdxRange},
    stmt::LnMirStmtArena,
    tactic::LnMirTacticArena,
};
use salsa::Db;
use std::ops::{Deref, DerefMut};
use visored_item_path::module::VdModulePath;
use visored_mir_expr::{
    expr::VdMirExprArenaRef,
    region::VdMirExprRegionData,
    stmt::VdMirStmtArenaRef,
    symbol::local_defn::{storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnIdx},
};

use crate::{
    dictionary::VdLeanDictionary, mangle::VdLeanTranspilationMangler,
    namespace::vd_module_path_to_ln_namespace,
};

pub struct VdLeanTranspilationBuilder<'a> {
    lean_hir_expr_builder: LnMirExprBuilder<'a>,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
    dictionary: &'a VdLeanDictionary,
    mangler: VdLeanTranspilationMangler,
    current_module_path: VdModulePath,
}

impl<'a> WithLnNamespace<'a> for VdLeanTranspilationBuilder<'a> {
    fn ln_mir_expr_builder_mut(&mut self) -> &mut LnMirExprBuilder<'a> {
        &mut self.lean_hir_expr_builder
    }
}

impl<'a> VdLeanTranspilationBuilder<'a> {
    pub fn new0(
        db: &'a ::salsa::Db,
        vd_mir_expr_region_data: &'a VdMirExprRegionData,
        dictionary: &'a VdLeanDictionary,
        root_module_path: VdModulePath,
    ) -> Self {
        Self::new(
            db,
            vd_mir_expr_region_data.expr_arena(),
            vd_mir_expr_region_data.stmt_arena(),
            vd_mir_expr_region_data.symbol_local_defn_storage(),
            dictionary,
            root_module_path,
        )
    }

    pub fn new(
        db: &'a ::salsa::Db,
        expr_arena: VdMirExprArenaRef<'a>,
        stmt_arena: VdMirStmtArenaRef<'a>,
        symbol_local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
        dictionary: &'a VdLeanDictionary,
        root_module_path: VdModulePath,
    ) -> Self {
        Self {
            lean_hir_expr_builder: LnMirExprBuilder::new(db),
            expr_arena,
            stmt_arena,
            dictionary,
            mangler: VdLeanTranspilationMangler::new(symbol_local_defn_storage, db),
            current_module_path: root_module_path,
        }
    }

    pub(crate) fn with_module_path<R>(
        &mut self,
        module_path: VdModulePath,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        debug_assert_eq!(
            module_path.parent(self.db()),
            Some(self.current_module_path),
            "module path = {}, current module path = {}",
            module_path.show(self.db()),
            self.current_module_path.show(self.db()),
        );
        let namespace = vd_module_path_to_ln_namespace(self.db(), module_path);
        let prev_module_path = self.current_module_path;
        self.current_module_path = module_path;
        let result = if let Some(namespace) = namespace {
            self.with_ln_namespace(namespace, f)
        } else {
            f(self)
        };
        self.current_module_path = prev_module_path;
        result
    }

    pub(crate) fn mangle_symbol(&mut self, symbol_local_defn: VdMirSymbolLocalDefnIdx) -> LnIdent {
        self.mangler.mangle_symbol(symbol_local_defn)
    }

    pub(crate) fn mangle_hypothesis(&mut self, db: &::salsa::Db) -> LnIdent {
        self.mangler.mangle_hypothesis(db)
    }

    pub(crate) fn sorry(&mut self) -> LnMirDefBody {
        LnMirDefBody::Expr(self.alloc_expr(LnMirExprData::Sorry))
    }
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub fn expr_arena(&self) -> VdMirExprArenaRef<'db> {
        self.expr_arena
    }

    pub fn stmt_arena(&self) -> VdMirStmtArenaRef<'db> {
        self.stmt_arena
    }

    pub fn dictionary(&self) -> &VdLeanDictionary {
        self.dictionary
    }
}

impl<'db> Deref for VdLeanTranspilationBuilder<'db> {
    type Target = LnMirExprBuilder<'db>;

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
    pub fn finish(
        self,
    ) -> (
        LnMirExprArena,
        LnMirStmtArena,
        LnMirTacticArena,
        LnItemDefnArena,
    ) {
        self.lean_hir_expr_builder.finish()
    }
}
