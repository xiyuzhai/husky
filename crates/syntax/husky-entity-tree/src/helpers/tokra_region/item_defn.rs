use husky_ast::range::AstTokenIdxRangeSheet;
use husky_item_defn_ast::{
    ItemDefnAst, ItemDefnAstArena, ItemDefnAstArenaRef, ItemDefnAstIdx, ItemDefnAstIdxRange,
};
use husky_regional_token::start::RegionalTokenVerseStart;
use husky_token::{TokenDb, TokenIdxRange, TokenSheetData};
use node::{ItemSynNodePathData, ItemSynNodePathId};

use super::*;

/// dedy is short for definition body
#[salsa::tracked]
pub struct ItemDefnTokraRegion {
    #[return_ref]
    _tokens_data: Vec<TokenData>,
    #[return_ref]
    ast_arena: ItemDefnAstArena,
    root_body: ItemDefnAstIdxRange,
    #[return_ref]
    token_verse_starts: Vec<RegionalTokenVerseStart>,
    #[return_ref]
    ast_token_idx_ranges: Vec<RegionalTokenIdxRange>,
    #[return_ref]
    nested_blocks: Vec<(
        RegionalTokenIdx, // lcurl
        ItemDefnAstIdxRange,
        Vec<RegionalTokenVerseStart>,
        RegionalTokenIdx, // end
    )>,
}

impl ItemDefnTokraRegion {
    pub fn data<'a>(self, db: &'a ::salsa::Db) -> ItemDefnTokraRegionDataRef<'a> {
        ItemDefnTokraRegionDataRef {
            tokens_data: self._tokens_data(db),
            ast_arena: self.ast_arena(db).as_arena_ref(),
            root_body: self.root_body(db),
            ast_token_idx_ranges: self.ast_token_idx_ranges(db),
            main_seq_token_verse_starts: self.token_verse_starts(db),
            nested_blocks: self.nested_blocks(db),
        }
    }

    pub fn tokens_data<'a>(self, db: &'a ::salsa::Db) -> RegionalTokensData<'a> {
        RegionalTokensData::new(self._tokens_data(db))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ItemDefnTokraRegionDataRef<'a> {
    tokens_data: &'a [TokenData],
    ast_arena: ItemDefnAstArenaRef<'a>,
    root_body: ItemDefnAstIdxRange,
    main_seq_token_verse_starts: &'a [RegionalTokenVerseStart],
    ast_token_idx_ranges: &'a [RegionalTokenIdxRange],
    nested_blocks: &'a [(
        RegionalTokenIdx,
        ItemDefnAstIdxRange,
        Vec<RegionalTokenVerseStart>,
        RegionalTokenIdx,
    )],
}

impl<'a> ItemDefnTokraRegionDataRef<'a> {
    #[inline(always)]
    pub fn root_body(self) -> ItemDefnAstIdxRange {
        self.root_body
    }

    #[inline(always)]
    pub fn ast_token_idx_range(self, defn_ast_idx: ItemDefnAstIdx) -> RegionalTokenIdxRange {
        self.ast_token_idx_ranges[defn_ast_idx.index()]
    }

    #[inline(always)]
    pub fn token_stream(
        self,
        regional_token_verse_idx: RegionalTokenVerseIdx,
    ) -> RegionalTokenStream<'a> {
        let token_verse_starts = if let Some(lcurl) = regional_token_verse_idx.lcurl() {
            self.nested_blocks
                .iter()
                .find_map(|&(lcurl1, _, ref token_verse_starts, _)| {
                    (lcurl == lcurl1).then_some(token_verse_starts)
                })
                .unwrap()
        } else {
            self.main_seq_token_verse_starts
        };
        let regional_token_verse_start = token_verse_starts[regional_token_verse_idx.index()];
        let start_index = regional_token_verse_start.index();
        let end_index = token_verse_starts
            .get(regional_token_verse_idx.index() + 1)
            .map(|&end| end.index())
            .unwrap_or(self.tokens_data.len());
        RegionalTokenStream::new_item_defn_regional_token_stream(
            &self.tokens_data[start_index..end_index],
            regional_token_verse_start,
        )
    }

    pub fn ast_arena(self) -> ItemDefnAstArenaRef<'a> {
        self.ast_arena
    }

    pub fn nested_block_ast_idx_range_and_end(
        &self,
        lcurl_regional_token_idx: RegionalTokenIdx,
    ) -> (ItemDefnAstIdxRange, RegionalTokenIdx) {
        self.nested_blocks
            .iter()
            .find_map(|&(lcurl_regional_token_idx1, defn_ast_idx_range, _, end)| {
                (lcurl_regional_token_idx == lcurl_regional_token_idx1)
                    .then_some((defn_ast_idx_range, end))
            })
            .unwrap()
    }
}

impl<'a> std::ops::Index<RegionalTokenIdx> for ItemDefnTokraRegionDataRef<'a> {
    type Output = TokenData;

    fn index(&self, idx: RegionalTokenIdx) -> &Self::Output {
        &self.tokens_data[idx.index()]
    }
}

impl<'a> std::ops::Index<RegionalTokenVerseIdx> for ItemDefnTokraRegionDataRef<'a> {
    type Output = [TokenData];

    fn index(&self, regional_token_verse_idx: RegionalTokenVerseIdx) -> &Self::Output {
        if let Some(_) = regional_token_verse_idx.lcurl() {
            todo!()
        }
        let start = self.main_seq_token_verse_starts[regional_token_verse_idx.index()].index();
        let end = self
            .main_seq_token_verse_starts
            .get(regional_token_verse_idx.index() + 1)
            .map(|&end| end.index())
            .unwrap_or(self.tokens_data.len());
        &self.tokens_data[start..end]
    }
}

impl<'a> std::ops::Index<ItemDefnAstIdx> for ItemDefnTokraRegionDataRef<'a> {
    type Output = ItemDefnAst;

    fn index(&self, idx: ItemDefnAstIdx) -> &Self::Output {
        &self.ast_arena[idx]
    }
}

#[salsa::tracked]
pub struct ItemDefnTokraRegionSourceMap {
    pub regional_token_verse_idx_base: RegionalTokenVerseIdxBase,
    pub regional_token_idx_base: RegionalTokenIdxBase,
    #[return_ref]
    pub ast_idx_map: Vec<AstIdx>,
}

impl ItemSynNodePathId {
    pub fn defn_tokra_region(self, db: &::salsa::Db) -> Option<ItemDefnTokraRegion> {
        Some(item_defn_tokra_region_with_source_map(db, self)?.0)
    }

    // use this only when necessary
    pub fn defn_tokra_region_source_map(
        self,
        db: &::salsa::Db,
    ) -> Option<ItemDefnTokraRegionSourceMap> {
        Some(item_defn_tokra_region_with_source_map(db, self)?.1)
    }

    pub fn defn_regional_token_idx_base(self, db: &::salsa::Db) -> Option<RegionalTokenIdxBase> {
        Some(
            self.defn_tokra_region_source_map(db)?
                .regional_token_idx_base(db),
        )
    }
}

#[salsa::tracked]
fn item_defn_tokra_region_with_source_map(
    db: &::salsa::Db,
    id: ItemSynNodePathId,
) -> Option<(ItemDefnTokraRegion, ItemDefnTokraRegionSourceMap)> {
    let builder = ItemDefnTokraRegionBuilder::new(id, db)?;
    Some(builder.build())
}

struct ItemDefnTokraRegionBuilder<'a> {
    ast_sheet: &'a AstSheet,
    ast_token_idx_range_sheet: &'a AstTokenIdxRangeSheet,
    defn_ast_arena: ItemDefnAstArena,
    root_body: AstIdxRange,
    regional_token_verse_idx_base: RegionalTokenVerseIdxBase,
    regional_token_idx_base: RegionalTokenIdxBase,
    token_sheet_data: &'a TokenSheetData,
    ast_idx_map: Vec<AstIdx>,
    regional_token_idx_range_map: Vec<RegionalTokenIdxRange>,
    tokens_data: Vec<TokenData>,
    db: &'a ::salsa::Db,
}

impl<'a> ItemDefnTokraRegionBuilder<'a> {
    fn new(id: ItemSynNodePathId, db: &'a ::salsa::Db) -> Option<Self> {
        let module_path = id.module_path(db);
        let opt_ast_idx = id.opt_ast_idx(db);
        let ast_sheet = module_path.ast_sheet(db);
        let root_body = match opt_ast_idx {
            Some(ast_idx) => match ast_sheet[ast_idx] {
                AstData::Identifiable { block, .. } => block.children()?,
                AstData::TypeVariant { .. } | AstData::Attr { .. } | AstData::ImplBlock { .. } => {
                    return None
                }
                ref ast => {
                    use salsa::DebugWithDb;
                    unreachable!(
                        "id unambiguous item path = {:?}, ast = {:?}",
                        id.unambiguous_item_path(db).debug(db),
                        ast
                    )
                }
            },
            None => match id.data(db) {
                ItemSynNodePathData::Script(_) => ast_sheet.top_level_asts(),
                ItemSynNodePathData::Submodule(_)
                | ItemSynNodePathData::MajorItem(_)
                | ItemSynNodePathData::TypeVariant(_)
                | ItemSynNodePathData::ImplBlock(_)
                | ItemSynNodePathData::AssocItem(_)
                | ItemSynNodePathData::Attr(_) => unreachable!(),
            },
        };
        let Some((first_ast_idx, first_token_verse_idx)) =
            root_body
                .into_iter()
                .find_map(|ast_idx| match ast_sheet[ast_idx] {
                    AstData::Err {
                        token_verse_idx, ..
                    }
                    | AstData::BasicStmtOrBranch {
                        token_verse_idx, ..
                    }
                    | AstData::MatchStmt {
                        token_verse_idx, ..
                    } => Some((ast_idx, token_verse_idx)),
                    AstData::IfElseStmts { if_branch, .. } => Some((
                        ast_idx,
                        match ast_sheet[if_branch] {
                            AstData::BasicStmtOrBranch {
                                token_verse_idx, ..
                            } => token_verse_idx,
                            _ => unreachable!(),
                        },
                    )),
                    _ => None,
                })
        else {
            // use husky_print_utils::p;
            // use salsa::DebugWithDb;
            // p!(id.unambiguous_item_path(db).debug(db));
            // unreachable!("should be guaranteed by a checker associated with trait `IsAstChildren` in `husky-ast` so that this is not reachable");
            return None;
        };
        let regional_token_verse_idx_base =
            RegionalTokenVerseIdxBase::from_token_verse_idx(first_token_verse_idx);
        let ast_token_idx_range_sheet = module_path.ast_token_idx_range_sheet(db);
        let token_sheet_data = db.token_sheet_data(module_path);
        let token_idx_range: TokenIdxRange = ast_token_idx_range_sheet[first_ast_idx]
            .join(ast_token_idx_range_sheet[root_body.end() - 1]);
        let tokens_data = token_sheet_data[token_idx_range].to_vec();
        let regional_token_idx_base = RegionalTokenIdxBase::new(
            token_sheet_data.token_verse_start(first_token_verse_idx),
            &tokens_data,
        );
        Some(Self {
            db,
            ast_sheet,
            defn_ast_arena: Default::default(),
            root_body,
            regional_token_verse_idx_base,
            tokens_data,
            regional_token_idx_base,
            token_sheet_data,
            ast_token_idx_range_sheet,
            ast_idx_map: Default::default(),
            regional_token_idx_range_map: Default::default(),
        })
    }

    fn build(mut self) -> (ItemDefnTokraRegion, ItemDefnTokraRegionSourceMap) {
        let root_body = self.build_asts(self.root_body);
        let asts_token_idx_range = self
            .ast_token_idx_range_sheet
            .asts_token_idx_range(self.root_body);
        let nested_seqs = self.build_nested_seqs(asts_token_idx_range);
        self.finish(root_body, nested_seqs)
    }

    fn build_asts(&mut self, ast_idx_range: AstIdxRange) -> ItemDefnAstIdxRange {
        let mut ast_idxs = vec![];
        let mut regional_token_idx_ranges = vec![];
        let mut regional_asts = vec![];
        for ast_idx in ast_idx_range {
            if let Some(regional_ast) = self.build_ast(ast_idx) {
                ast_idxs.push(ast_idx);
                regional_token_idx_ranges.push(RegionalTokenIdxRange::from_token_idx_range(
                    self.ast_token_idx_range_sheet[ast_idx],
                    self.regional_token_idx_base,
                ));
                regional_asts.push(regional_ast)
            }
        }
        let regional_ast_idx_range = self.defn_ast_arena.alloc_many(regional_asts);
        debug_assert_eq!(
            regional_ast_idx_range.start().index(),
            self.ast_idx_map.len()
        );
        debug_assert_eq!(
            regional_ast_idx_range.start().index(),
            self.regional_token_idx_range_map.len()
        );
        self.ast_idx_map.extend(ast_idxs);
        self.regional_token_idx_range_map
            .extend(regional_token_idx_ranges);
        regional_ast_idx_range
    }

    fn build_ast(&mut self, ast_idx: AstIdx) -> Option<ItemDefnAst> {
        match self.ast_sheet[ast_idx] {
            AstData::Err { .. } => Some(ItemDefnAst::Err),
            AstData::BasicStmtOrBranch {
                token_verse_idx,
                body,
            } => Some(ItemDefnAst::BasicStmtOrBranch {
                regional_token_verse_idx: RegionalTokenVerseIdx::new(
                    token_verse_idx,
                    self.regional_token_verse_idx_base,
                    self.regional_token_idx_base,
                ),
                body: body.map(|body| self.build_asts(body.ast_idx_range())),
            }),
            AstData::IfElseStmts {
                if_branch,
                elif_branches,
                else_branch,
            } => Some(ItemDefnAst::IfElseStmts {
                if_branch: self.build_ast_then_alloc(if_branch).expect("todo"),
                elif_branches: self.build_asts(elif_branches),
                else_branch: else_branch
                    .map(|else_branch| self.build_ast_then_alloc(else_branch).expect("todo")),
            }),
            AstData::MatchStmt {
                token_verse_idx,
                pattern_stmt,
                case_branches,
            } => Some(ItemDefnAst::MatchStmt {
                regional_token_verse_idx: RegionalTokenVerseIdx::new(
                    token_verse_idx,
                    self.regional_token_verse_idx_base,
                    self.regional_token_idx_base,
                ),
                pattern_stmt: self.build_ast_then_alloc(pattern_stmt).expect("todo"),
                case_branches: self.build_asts(case_branches),
            }),
            _ => None,
        }
    }

    fn build_ast_then_alloc(&mut self, ast_idx: AstIdx) -> Option<ItemDefnAstIdx> {
        let regional_ast = self.build_ast(ast_idx)?;
        let regional_ast_idx = self.defn_ast_arena.alloc_one(regional_ast);
        self.ast_idx_map.push(ast_idx);
        self.regional_token_idx_range_map
            .push(RegionalTokenIdxRange::from_token_idx_range(
                self.ast_token_idx_range_sheet[ast_idx],
                self.regional_token_idx_base,
            ));
        Some(regional_ast_idx)
    }

    fn build_nested_seqs(
        &mut self,
        asts_token_idx_range: TokenIdxRange,
    ) -> Vec<(
        RegionalTokenIdx,
        ArenaIdxRange<ItemDefnAst>,
        Vec<RegionalTokenVerseStart>,
        RegionalTokenIdx,
    )> {
        let nested_seqs: Vec<_> = self
            .ast_sheet
            .nested_top_level_asts()
            .iter()
            .copied()
            .filter_map(|(token_idx, ast_idx_range)| {
                asts_token_idx_range.contains(token_idx).then(|| {
                    let nested_token_verse_sequence =
                        &self.token_sheet_data.token_verses().nested_sequences()[token_idx];
                    let verse_starts = nested_token_verse_sequence
                        .verses_data()
                        .iter()
                        .map(|verse| {
                            RegionalTokenVerseStart::from_token_verse_start(
                                verse.start(),
                                self.regional_token_idx_base,
                            )
                        })
                        .collect();
                    (
                        RegionalTokenIdx::from_token_idx(token_idx, self.regional_token_idx_base),
                        self.build_asts(ast_idx_range),
                        verse_starts,
                        RegionalTokenIdx::from_token_idx(
                            nested_token_verse_sequence.end(),
                            self.regional_token_idx_base,
                        ),
                    )
                })
            })
            .collect();
        nested_seqs
    }

    fn finish(
        self,
        root_body: ItemDefnAstIdxRange,
        nested_seqs: Vec<(
            RegionalTokenIdx,
            ItemDefnAstIdxRange,
            Vec<RegionalTokenVerseStart>,
            RegionalTokenIdx,
        )>,
    ) -> (ItemDefnTokraRegion, ItemDefnTokraRegionSourceMap) {
        // todo: nested??
        let token_verses = self.token_sheet_data.token_verses();
        let verses_data = token_verses.main_sequence().verses_data();
        let verse_starts = (self.regional_token_verse_idx_base.index()..)
            .into_iter()
            .map_while(|token_verse_index| {
                let token_verse_start = verses_data.get(token_verse_index)?.start();
                if self.regional_token_idx_base.index_base() + self.tokens_data.len()
                    <= token_verse_start.index()
                {
                    return None;
                }
                Some(RegionalTokenVerseStart::from_token_verse_start(
                    token_verse_start,
                    self.regional_token_idx_base,
                ))
            })
            .collect();
        (
            ItemDefnTokraRegion::new(
                self.db,
                self.tokens_data,
                self.defn_ast_arena,
                root_body,
                verse_starts,
                self.regional_token_idx_range_map,
                nested_seqs,
            ),
            ItemDefnTokraRegionSourceMap::new(
                self.db,
                self.regional_token_verse_idx_base,
                self.regional_token_idx_base,
                self.ast_idx_map,
            ),
        )
    }
}
