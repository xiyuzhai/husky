mod debug;
mod helpers;

use eterned::db::EternerDb;
use latex_token::storage::LxTokenStorage;
use lean_coword::ident::LnIdent;
use lean_entity_path::menu::{ln_item_path_menu, LnItemPathMenu};
use lean_mir_expr::{
    constructor::{LnMirExprConstructor, WithLnNamespace},
    expr::{LnMirExprArena, LnMirExprData, LnMirExprEntry},
    item_defn::{
        def::LnMirDefBody, LnItemDefnArena, LnItemDefnComment, LnItemDefnCommentMap,
        LnItemDefnData, LnItemDefnIdxRange,
    },
    stmt::LnMirStmtArena,
    tactic::LnMirTacticArena,
};
use std::ops::{Deref, DerefMut};
use visored_entity_path::module::VdModulePath;
use visored_mir_expr::{
    derivation::{VdMirDerivationArenaRef, VdMirDerivationIdx},
    expr::VdMirExprArenaRef,
    hint::VdMirHintArenaRef,
    hypothesis::{chunk::VdMirHypothesisChunk, VdMirHypothesisArenaRef, VdMirHypothesisIdx},
    region::VdMirExprRegionData,
    source_map::VdMirRegionSourceMap,
    stmt::VdMirStmtArenaRef,
    symbol::local_defn::{storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnIdx},
};
use visored_sem_expr::range::{
    VdSemBlockTokenIdxRangeMap, VdSemClauseTokenIdxRangeMap, VdSemDivisionTokenIdxRangeMap,
    VdSemExprTokenIdxRangeMap, VdSemPhraseTokenIdxRangeMap, VdSemSentenceTokenIdxRangeMap,
};
use visored_term::menu::{vd_ty_menu, VdTypeMenu};

use crate::{
    dictionary::VdLeanDictionary,
    mangle::VdLeanTranspilationMangler,
    namespace::{vd_module_path_to_ln_namespace, vd_module_path_to_ln_namespace_or_inherited},
    scheme::IsVdLeanTranspilationScheme,
};

pub struct VdLeanTranspilationBuilder<'a, S: IsVdLeanTranspilationScheme> {
    db: &'a EternerDb,
    scheme: &'a S,
    input: &'a str,
    ln_item_path_menu: &'a LnItemPathMenu,
    ty_menu: &'a VdTypeMenu,
    lean_hir_expr_constructor: LnMirExprConstructor,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
    hint_arena: VdMirHintArenaRef<'a>,
    hypothesis_arena: VdMirHypothesisArenaRef<'a>,
    derivation_arena: VdMirDerivationArenaRef<'a>,
    dictionary: &'a VdLeanDictionary,
    mangler: VdLeanTranspilationMangler,
    current_module_path: VdModulePath,
    source_map: &'a VdMirRegionSourceMap,
    sem_expr_range_map: &'a VdSemExprTokenIdxRangeMap,
    sem_phrase_range_map: &'a VdSemPhraseTokenIdxRangeMap,
    sem_clause_range_map: &'a VdSemClauseTokenIdxRangeMap,
    sem_sentence_range_map: &'a VdSemSentenceTokenIdxRangeMap,
    sem_stmt_range_map: &'a VdSemBlockTokenIdxRangeMap,
    sem_division_range_map: &'a VdSemDivisionTokenIdxRangeMap,
    token_storage: &'a LxTokenStorage,
    cache: S::Cache,
}

impl<'a, S> WithLnNamespace for VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    fn ln_mir_expr_builder_mut(&mut self) -> &mut LnMirExprConstructor {
        &mut self.lean_hir_expr_constructor
    }
}

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub fn new0(
        db: &'a EternerDb,
        scheme: &'a S,
        input: &'a str,
        vd_mir_expr_region_data: &'a VdMirExprRegionData,
        source_map: &'a VdMirRegionSourceMap,
        dictionary: &'a VdLeanDictionary,
        root_module_path: VdModulePath,
        sem_expr_range_map: &'a VdSemExprTokenIdxRangeMap,
        sem_phrase_range_map: &'a VdSemPhraseTokenIdxRangeMap,
        sem_clause_range_map: &'a VdSemClauseTokenIdxRangeMap,
        sem_sentence_range_map: &'a VdSemSentenceTokenIdxRangeMap,
        sem_stmt_range_map: &'a VdSemBlockTokenIdxRangeMap,
        sem_division_range_map: &'a VdSemDivisionTokenIdxRangeMap,
        token_storage: &'a LxTokenStorage,
    ) -> Self {
        Self::new(
            db,
            scheme,
            input,
            vd_mir_expr_region_data.expr_arena(),
            vd_mir_expr_region_data.stmt_arena(),
            vd_mir_expr_region_data.hint_arena(),
            vd_mir_expr_region_data.hypothesis_arena(),
            vd_mir_expr_region_data.derivation_arena(),
            vd_mir_expr_region_data.symbol_local_defn_storage(),
            source_map,
            dictionary,
            root_module_path,
            sem_expr_range_map,
            sem_phrase_range_map,
            sem_clause_range_map,
            sem_sentence_range_map,
            sem_stmt_range_map,
            sem_division_range_map,
            token_storage,
        )
    }

    pub fn new(
        db: &'a EternerDb,
        scheme: &'a S,
        input: &'a str,
        expr_arena: VdMirExprArenaRef<'a>,
        stmt_arena: VdMirStmtArenaRef<'a>,
        hint_arena: VdMirHintArenaRef<'a>,
        hypothesis_arena: VdMirHypothesisArenaRef<'a>,
        derivation_arena: VdMirDerivationArenaRef<'a>,
        symbol_local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
        source_map: &'a VdMirRegionSourceMap,
        dictionary: &'a VdLeanDictionary,
        root_module_path: VdModulePath,
        sem_expr_range_map: &'a VdSemExprTokenIdxRangeMap,
        sem_phrase_range_map: &'a VdSemPhraseTokenIdxRangeMap,
        sem_clause_range_map: &'a VdSemClauseTokenIdxRangeMap,
        sem_sentence_range_map: &'a VdSemSentenceTokenIdxRangeMap,
        sem_stmt_range_map: &'a VdSemBlockTokenIdxRangeMap,
        sem_division_range_map: &'a VdSemDivisionTokenIdxRangeMap,
        token_storage: &'a LxTokenStorage,
    ) -> Self {
        Self {
            db,
            scheme,
            ln_item_path_menu: &ln_item_path_menu,
            ty_menu: vd_ty_menu(db),
            lean_hir_expr_constructor: LnMirExprConstructor::new(db),
            expr_arena,
            stmt_arena,
            hint_arena,
            hypothesis_arena,
            derivation_arena,
            source_map,
            dictionary,
            mangler: VdLeanTranspilationMangler::new(
                hypothesis_arena,
                derivation_arena,
                symbol_local_defn_storage,
                db,
            ),
            current_module_path: root_module_path,
            sem_expr_range_map,
            sem_phrase_range_map,
            sem_clause_range_map,
            sem_sentence_range_map,
            sem_stmt_range_map,
            sem_division_range_map,
            token_storage,
            input,
            cache: S::Cache::default(),
        }
    }

    pub(crate) fn with_module_path<R>(
        &mut self,
        module_path: VdModulePath,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let db = self.db();
        debug_assert_eq!(
            module_path.parent(),
            Some(self.current_module_path),
            "module path = {}, current module path = {}",
            module_path.show(),
            self.current_module_path.show(),
        );
        let namespace = vd_module_path_to_ln_namespace(module_path, db);
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

    pub(crate) fn current_module_path(&self) -> VdModulePath {
        self.current_module_path
    }

    pub(crate) fn ty_menu(&self) -> &'a VdTypeMenu {
        self.ty_menu
    }

    pub(crate) fn mangle_symbol(&mut self, symbol_local_defn: VdMirSymbolLocalDefnIdx) -> LnIdent {
        self.mangler.mangle_symbol(symbol_local_defn)
    }

    pub(crate) fn mangle_hypothesis(&mut self, hypothesis: VdMirHypothesisIdx) -> LnIdent {
        let db = self.db();
        self.mangler.mangle_hypothesis(
            hypothesis,
            vd_module_path_to_ln_namespace_or_inherited(self.current_module_path, db),
            db,
        )
    }

    pub(crate) fn mangle_old_main_hypothesis(&mut self) -> LnIdent {
        // TODO: This is a temporary hack to get the old main hypothesis to work.
        self.new_hypothesis_ident()
    }

    pub(crate) fn mangle_stmts_item_defn(&mut self) -> LnIdent {
        // TODO: This is a temporary hack to get the old main hypothesis to work.
        self.new_hypothesis_ident()
    }

    /// TODO: This is a temporary hack to get the old main hypothesis to work.
    pub(crate) fn new_hypothesis_ident(&mut self) -> LnIdent {
        self.mangler.new_hypothesis_ident(
            vd_module_path_to_ln_namespace_or_inherited(self.current_module_path, self.db()),
            self.db(),
        )
    }

    pub(crate) fn mangle_assume(&mut self, hypothesis_chunk: VdMirHypothesisChunk) -> LnIdent {
        self.mangle_hypothesis(hypothesis_chunk.main_hypothesis())
    }

    pub(crate) fn mangle_derivation(&mut self, derivation: VdMirDerivationIdx) -> LnIdent {
        let db = self.db();
        self.mangler.mangle_derivation(
            derivation,
            vd_module_path_to_ln_namespace_or_inherited(self.current_module_path, db),
            db,
        )
    }

    pub(crate) fn sorry(&mut self) -> LnMirDefBody {
        LnMirDefBody::Expr(self.alloc_expr(LnMirExprEntry::new(LnMirExprData::Sorry)))
    }
}

impl<'db, Scheme> VdLeanTranspilationBuilder<'db, Scheme>
where
    Scheme: IsVdLeanTranspilationScheme,
{
    pub fn db(&self) -> &'db EternerDb {
        self.db
    }

    pub fn expr_arena(&self) -> VdMirExprArenaRef<'db> {
        self.expr_arena
    }

    pub fn stmt_arena(&self) -> VdMirStmtArenaRef<'db> {
        self.stmt_arena
    }

    pub fn hint_arena(&self) -> VdMirHintArenaRef<'db> {
        self.hint_arena
    }

    pub fn hypothesis_arena(&self) -> VdMirHypothesisArenaRef<'db> {
        self.hypothesis_arena
    }

    pub fn derivation_arena(&self) -> VdMirDerivationArenaRef<'db> {
        self.derivation_arena
    }

    pub fn source_map(&self) -> &'db VdMirRegionSourceMap {
        self.source_map
    }

    pub fn dictionary(&self) -> &'db VdLeanDictionary {
        self.dictionary
    }

    pub fn input(&self) -> &'db str {
        self.input
    }

    pub fn token_storage(&self) -> &'db LxTokenStorage {
        self.token_storage
    }

    pub fn sem_expr_range_map(&self) -> &'db VdSemExprTokenIdxRangeMap {
        self.sem_expr_range_map
    }

    pub fn sem_phrase_range_map(&self) -> &'db VdSemPhraseTokenIdxRangeMap {
        self.sem_phrase_range_map
    }

    pub fn sem_clause_range_map(&self) -> &'db VdSemClauseTokenIdxRangeMap {
        self.sem_clause_range_map
    }

    pub fn sem_sentence_range_map(&self) -> &'db VdSemSentenceTokenIdxRangeMap {
        self.sem_sentence_range_map
    }

    pub fn sem_stmt_range_map(&self) -> &'db VdSemBlockTokenIdxRangeMap {
        self.sem_stmt_range_map
    }

    pub fn sem_division_range_map(&self) -> &'db VdSemDivisionTokenIdxRangeMap {
        self.sem_division_range_map
    }

    pub fn cache(&self) -> &Scheme::Cache {
        &self.cache
    }
}

impl<'db, Scheme> VdLeanTranspilationBuilder<'db, Scheme>
where
    Scheme: IsVdLeanTranspilationScheme,
{
    pub fn cache_mut(&mut self) -> &mut Scheme::Cache {
        &mut self.cache
    }
}

impl<'db, S> Deref for VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    type Target = LnMirExprConstructor;

    fn deref(&self) -> &Self::Target {
        &self.lean_hir_expr_constructor
    }
}

impl<'db, S> DerefMut for VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lean_hir_expr_constructor
    }
}

impl<'db, S> VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub fn finish(
        self,
    ) -> (
        LnMirExprArena,
        LnMirStmtArena,
        LnMirTacticArena,
        LnItemDefnArena,
        LnItemDefnCommentMap,
    ) {
        self.lean_hir_expr_constructor.finish()
    }
}
