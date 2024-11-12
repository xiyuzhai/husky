mod root;
mod stmt;

pub use self::root::*;

use crate::*;
use husky_entity_tree::{
    helpers::tokra_region::TokraRegionDataRef, jar::EntityTreeDb, node::ItemSynNodePath,
    region_path::SynNodeRegionPath, symbol::ModuleSymbolContext,
};
use husky_vfs::path::module_path::ModulePath;
use repl::ReplSource;

pub struct SynExprContext<'a> {
    db: &'a ::salsa::Db,
    path: SynNodeRegionPath,
    module_path: ModulePath,
    crate_root_path: ModulePath,
    parent_syn_expr_region: Option<SynExprRegion>,
    variable_context: VariableContextMut<'a>,
    syn_expr_arena: SynExprArena,
    syn_principal_entity_path_expr_arena: SynPrincipalEntityPathExprArena,
    syn_pattern_region: SynPatternRegion,
    syn_stmt_arena: SynStmtArena,
    syn_pattern_roots: Vec<SynPatternRoot>,
    syn_expr_roots: Vec<SynExprRoot>,
    has_self_lifetime: bool,
    has_self_place: bool,
    tokra_region_data: TokraRegionDataRef<'a>,
}

pub trait IsSynExprContext<'a>:
    std::borrow::Borrow<SynExprContext<'a>> + std::borrow::BorrowMut<SynExprContext<'a>>
{
}

impl<'a> IsSynExprContext<'a> for SynExprContext<'a> {}

impl<'a, 'b> IsSynExprContext<'a> for &'b mut SynExprContext<'a> {}

impl<'a> SynExprContext<'a> {
    pub fn new(
        module_path: ModulePath,
        syn_node_region_path: SynNodeRegionPath,
        decl_expr_region: impl Into<Option<SynExprRegion>>,
        allow_self_type: AllowSelfType,
        allow_self_value: AllowSelfValue,
        repl_src: Option<ReplSource>,
        db: &'a ::salsa::Db,
    ) -> Option<Self> {
        Self::new2(
            db,
            syn_node_region_path,
            db.module_symbol_context(module_path).unwrap(),
            decl_expr_region.into(),
            allow_self_type,
            allow_self_value,
            repl_src,
        )
    }

    pub fn new2(
        db: &'a ::salsa::Db,
        path: SynNodeRegionPath,
        module_symbol_context: ModuleSymbolContext<'a>,
        parent_expr_region: Option<SynExprRegion>,
        allow_self_type: AllowSelfType,
        allow_self_value: AllowSelfValue,
        repl_src: Option<ReplSource>,
    ) -> Option<Self> {
        let module_path = path.module_path(db);
        Some(Self {
            db,
            path,
            module_path,
            crate_root_path: module_path.root_module_path(db),
            parent_syn_expr_region: parent_expr_region,
            variable_context: VariableContextMut::new(
                module_symbol_context,
                parent_expr_region.map(|er| er.data(db).variable_region()),
                allow_self_type,
                allow_self_value,
                repl_src,
            ),
            syn_expr_arena: Default::default(),
            syn_principal_entity_path_expr_arena: Default::default(),
            syn_pattern_region: Default::default(),
            syn_stmt_arena: Default::default(),
            syn_pattern_roots: vec![],
            syn_expr_roots: vec![],
            has_self_lifetime: false,
            has_self_place: false,
            tokra_region_data: path.tokra_region_data_ref(db)?,
        })
    }

    pub fn finish(self) -> SynExprRegion {
        self.variable_context.into_expr_region(
            self.db,
            self.parent_syn_expr_region,
            self.path,
            self.syn_expr_arena,
            self.syn_principal_entity_path_expr_arena,
            self.syn_pattern_region,
            self.syn_stmt_arena,
            self.syn_pattern_roots,
            self.syn_expr_roots,
            self.has_self_lifetime,
            self.has_self_place,
        )
    }

    pub fn token_verse_expr_parser<'b>(
        &'b mut self,
        token_verse_idx: RegionalTokenVerseIdx,
    ) -> SynExprParser<'a, &'b mut SynExprContext<'a>>
    where
        'a: 'b,
    {
        let token_stream = self.token_verse_token_stream(token_verse_idx);
        SynExprParser::new(self, None, token_stream)
    }

    pub fn token_stream_expr_parser(
        self,
        env: Option<ExprEnvironment>,
        token_stream: RegionalTokenStream<'a>,
    ) -> StandaloneSynExprParser<'a> {
        SynExprParser::new(self, env, token_stream)
    }

    pub(crate) fn pattern_region(&self) -> &SynPatternRegion {
        &self.syn_pattern_region
    }

    #[inline(always)]
    pub(crate) fn define_symbol(
        &mut self,
        variable: CurrentVariableEntry,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdx {
        self.variable_context.define_symbol(variable, ty_constraint)
    }

    #[inline(always)]
    pub(crate) fn define_symbols(
        &mut self,
        variables: impl IntoIterator<Item = CurrentVariableEntry>,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdxRange {
        self.variable_context
            .define_symbols(variables, ty_constraint)
    }

    pub fn db(&self) -> &'a ::salsa::Db {
        self.db
    }

    pub fn syn_expr_arena(&self) -> &SynExprArena {
        &self.syn_expr_arena
    }

    pub fn variable_context(&self) -> &VariableContextMut<'a> {
        &self.variable_context
    }

    pub fn module_path(&self) -> ModulePath {
        self.module_path
    }

    pub fn syn_pattern_region(&self) -> &SynPatternRegion {
        &self.syn_pattern_region
    }

    pub(crate) fn syn_expr_arena_mut(&mut self) -> &mut SynExprArena {
        &mut self.syn_expr_arena
    }

    pub(crate) fn alloc_expr(&mut self, syn_expr: SynExprData) -> SynExprIdx {
        self.syn_expr_arena.alloc_one(syn_expr)
    }

    pub(crate) fn alloc_inline_stmt(&mut self, syn_stmt: SynStmtData) -> SynStmtIdxRange {
        SynStmtIdxRange::new_single(self.syn_stmt_arena.alloc_one(syn_stmt))
    }

    pub(super) fn alloc_stmts(&mut self, syn_stmts: Vec<SynStmtData>) -> SynStmtIdxRange {
        self.syn_stmt_arena.alloc_batch(syn_stmts)
    }

    pub(crate) fn alloc_pattern(&mut self, expr: SynPatternData) -> SynPatternIdx {
        self.syn_pattern_region.alloc_one_pattern(expr)
    }

    pub(crate) fn alloc_item_path_expr(
        &mut self,
        expr: SynPrincipalEntityPathExpr,
    ) -> SynPrincipalEntityPathExprIdx {
        self.syn_principal_entity_path_expr_arena.alloc_one(expr)
    }

    pub fn crate_root_path(&self) -> ModulePath {
        self.crate_root_path
    }

    pub fn set_has_self_lifetime(&mut self) {
        debug_assert!(!self.has_self_lifetime);
        self.has_self_lifetime = true;
    }

    pub fn set_has_self_place(&mut self) {
        debug_assert!(!self.has_self_place);
        self.has_self_place = true;
    }

    pub fn syn_principal_entity_path_expr_arena(&self) -> &SynPrincipalEntityPathExprArena {
        &self.syn_principal_entity_path_expr_arena
    }

    pub(crate) fn tokra_region_data(&self) -> TokraRegionDataRef<'a> {
        self.tokra_region_data
    }

    pub(crate) fn set_abstract_variable_access_end(
        &mut self,
        var: CurrentVariableIdx,
        access_end: RegionalTokenIdxRangeEnd,
    ) {
        self.variable_context
            .set_abstract_variable_access_end(var, access_end)
    }
}
