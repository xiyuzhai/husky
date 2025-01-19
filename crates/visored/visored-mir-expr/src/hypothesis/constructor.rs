mod expr;
mod signature;

use std::any::Any;

use super::{
    chunk::VdMirHypothesisChunk, construction::VdMirHypothesisConstruction, VdMirHypothesisArena,
    VdMirHypothesisArenaRef, VdMirHypothesisIdx,
};
use crate::{
    derivation::{
        chunk::VdMirDerivationChunk, construction::VdMirDerivationConstruction,
        VdMirDerivationArena, VdMirDerivationArenaRef, VdMirDerivationEntry, VdMirDerivationIdx,
        VdMirDerivationIdxRange,
    },
    expr::{
        VdMirExprArena, VdMirExprArenaRef, VdMirExprData, VdMirExprEntry, VdMirExprIdx,
        VdMirExprIdxRange,
    },
    hint::{VdMirHintArena, VdMirHintArenaRef},
    hypothesis::{VdMirHypothesisEntry, VdMirHypothesisIdxRange},
    region::VdMirExprRegionDataRef,
    stmt::{VdMirStmtArena, VdMirStmtArenaRef, VdMirStmtIdx},
    symbol::local_defn::storage::VdMirSymbolLocalDefnStorage,
};
use eterned::db::EternerDb;
use rustc_hash::FxHashMap;
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_term::{
    menu::{vd_ty_menu, VdTypeMenu},
    term::literal::VdLiteral,
    ty::VdType,
};

pub struct VdMirHypothesisConstructor<'db, Src> {
    db: &'db EternerDb,
    ty_menu: &'db VdTypeMenu,
    default_global_dispatch_table: VdDefaultGlobalDispatchTable,
    expr_arena: VdMirExprArena,
    stmt_arena: VdMirStmtArena,
    hint_arena: VdMirHintArena,
    hypothesis_arena: VdMirHypothesisArena,
    derivation_arena: VdMirDerivationArena,
    symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    current_stmt_and_hypothesis_chunk_start: Option<(VdMirStmtIdx, VdMirHypothesisIdx)>,
    current_derivation_chunk_start: Option<VdMirDerivationIdx>,
    cache: FxHashMap<Src, VdMirHypothesisIdx>,
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn new(
        db: &'db EternerDb,
        default_global_dispatch_table: VdDefaultGlobalDispatchTable,
        expr_arena: VdMirExprArena,
        stmt_arena: VdMirStmtArena,
        hint_arena: VdMirHintArena,
        symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            db,
            ty_menu: vd_ty_menu(db),
            default_global_dispatch_table,
            expr_arena,
            stmt_arena,
            hint_arena,
            symbol_local_defn_storage,
            hypothesis_arena: Default::default(),
            derivation_arena: Default::default(),
            current_stmt_and_hypothesis_chunk_start: None,
            current_derivation_chunk_start: None,
            cache: FxHashMap::default(),
        }
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn default_global_dispatch_table(&self) -> &VdDefaultGlobalDispatchTable {
        &self.default_global_dispatch_table
    }

    pub fn expr_arena(&self) -> VdMirExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn expr(&self, idx: VdMirExprIdx) -> &VdMirExprEntry {
        &self.expr_arena[idx]
    }

    #[track_caller]
    pub fn literal(&self, idx: VdMirExprIdx) -> &VdLiteral {
        match self.expr_arena[idx].data() {
            VdMirExprData::Literal(vd_literal) => vd_literal,
            _ => panic!("expected literal, got `{:?}`", self.expr_arena[idx].data()),
        }
    }

    pub fn stmt_arena(&self) -> VdMirStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }

    pub fn stmt_arena_mut(&mut self) -> &mut VdMirStmtArena {
        &mut self.stmt_arena
    }

    pub fn hint_arena(&self) -> VdMirHintArenaRef {
        self.hint_arena.as_arena_ref()
    }

    pub fn hypothesis_arena(&self) -> VdMirHypothesisArenaRef {
        self.hypothesis_arena.as_arena_ref()
    }

    pub fn derivation_arena(&self) -> &VdMirDerivationArena {
        &self.derivation_arena
    }

    pub fn derivation_arena_ref(&self) -> VdMirDerivationArenaRef {
        self.derivation_arena.as_arena_ref()
    }

    pub fn region_data(&self) -> VdMirExprRegionDataRef {
        VdMirExprRegionDataRef {
            default_global_dispatch_table: &self.default_global_dispatch_table,
            expr_arena: self.expr_arena.as_arena_ref(),
            stmt_arena: self.stmt_arena.as_arena_ref(),
            hint_arena: self.hint_arena.as_arena_ref(),
            symbol_local_defn_storage: &self.symbol_local_defn_storage,
        }
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub(crate) fn obtain_hypothesis_chunk_within_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        f: impl FnOnce(&mut Self) -> VdMirHypothesisIdx,
    ) -> VdMirHypothesisChunk {
        assert!(self.current_stmt_and_hypothesis_chunk_start.is_none());
        assert!(self.current_derivation_chunk_start.is_none());
        self.current_stmt_and_hypothesis_chunk_start = Some((stmt, unsafe {
            VdMirHypothesisIdx::new_ext(self.hypothesis_arena.len())
        }));
        let result = f(self);
        let Some((stmt, chunk_start)) = self.current_stmt_and_hypothesis_chunk_start else {
            unreachable!()
        };
        self.current_stmt_and_hypothesis_chunk_start = None;
        VdMirHypothesisChunk::new(
            stmt,
            unsafe {
                VdMirHypothesisIdxRange::new(chunk_start, unsafe {
                    VdMirHypothesisIdx::new_ext(self.hypothesis_arena.len())
                })
            },
            result,
        )
    }

    // TODO: do more things like handle hypothesis stack, register src, etc.
    pub fn construct_new_hypothesis(
        &mut self,
        src: Src,
        f: impl FnOnce(&mut Self) -> (VdMirExprIdx, VdMirHypothesisConstruction),
    ) -> VdMirHypothesisIdx
    where
        Src: std::hash::Hash + Eq,
    {
        assert!(self.current_stmt_and_hypothesis_chunk_start.is_some());
        if let Some(&hypothesis) = self.cache.get(&src) {
            return hypothesis;
        }
        let (expr, hypothesis) = f(self);
        let hypothesis = self
            .hypothesis_arena
            .alloc_one(VdMirHypothesisEntry::new(expr, hypothesis));
        self.cache.insert(src, hypothesis);
        hypothesis
    }

    pub fn obtain_derivation_chunk_within_hypothesis(
        &mut self,
        f: impl FnOnce(&mut Self) -> VdMirDerivationIdx,
    ) -> VdMirDerivationChunk {
        assert!(self.current_stmt_and_hypothesis_chunk_start.is_some());
        assert!(self.current_derivation_chunk_start.is_none());
        self.current_derivation_chunk_start =
            Some(unsafe { VdMirDerivationIdx::new_ext(self.derivation_arena.len()) });
        let result = f(self);
        let Some(chunk_start) = self.current_derivation_chunk_start else {
            unreachable!()
        };
        self.current_derivation_chunk_start = None;
        VdMirDerivationChunk::new(
            unsafe {
                VdMirDerivationIdxRange::new(chunk_start, unsafe {
                    VdMirDerivationIdx::new_ext(self.derivation_arena.len())
                })
            },
            result,
        )
    }

    pub fn alloc_derivation(
        &mut self,
        prop: VdMirExprIdx,
        construction: VdMirDerivationConstruction,
    ) -> VdMirDerivationIdx {
        let entry = VdMirDerivationEntry::new(prop, construction, self);
        self.derivation_arena.alloc_one(entry)
    }

    pub(crate) fn finish(
        self,
    ) -> (
        VdDefaultGlobalDispatchTable,
        VdMirExprArena,
        VdMirStmtArena,
        VdMirHintArena,
        VdMirHypothesisArena,
        VdMirDerivationArena,
        VdMirSymbolLocalDefnStorage,
    ) {
        (
            self.default_global_dispatch_table,
            self.expr_arena,
            self.stmt_arena,
            self.hint_arena,
            self.hypothesis_arena,
            self.derivation_arena,
            self.symbol_local_defn_storage,
        )
    }
}
