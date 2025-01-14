use super::*;
use husky_ast::range::AstTokenIdxRangeSheet;
use husky_crate_decl_ast::{
    CrateDeclAst, CrateDeclAstArena, CrateDeclAstArenaRef, CrateDeclAstIdx, CrateDeclAstIdxRange,
};
use husky_token::{TokenDb, TokenIdxRange};
use start::RegionalTokenVerseStart;

#[salsa::tracked(constructor = new)]
pub struct CrateDeclTokraRegion {
    #[return_ref]
    tokens_data: Vec<TokenData>,
    #[return_ref]
    ast_arena: CrateDeclAstArena,
    root_body: CrateDeclAstIdxRange,
    #[return_ref]
    token_verse_starts: Vec<RegionalTokenVerseStart>,
    #[return_ref]
    ast_token_idx_ranges: Vec<RegionalTokenIdxRange>,
}

#[derive(Debug, Clone, Copy)]
pub struct CrateDeclTokraRegionDataRef<'db> {
    ast_arena: CrateDeclAstArenaRef<'db>,
    root_body: CrateDeclAstIdxRange,
    tokens_data: &'db [TokenData],
    token_verse_starts: &'db [RegionalTokenVerseStart],
}

impl<'a> std::ops::Index<RegionalTokenIdx> for CrateDeclTokraRegionDataRef<'a> {
    type Output = TokenData;

    fn index(&self, idx: RegionalTokenIdx) -> &Self::Output {
        &self.tokens_data[idx.index()]
    }
}

impl<'a> std::ops::Index<CrateDeclAstIdx> for CrateDeclTokraRegionDataRef<'a> {
    type Output = CrateDeclAst;

    fn index(&self, idx: CrateDeclAstIdx) -> &Self::Output {
        &self.ast_arena[idx]
    }
}

#[salsa::tracked]
pub struct CrateDeclTokraRegionSourceMap {
    pub regional_token_verse_idx_base: RegionalTokenVerseIdxBase,
    pub regional_token_idx_base: RegionalTokenIdxBase,
    #[return_ref]
    pub ast_idx_map: Vec<AstIdx>,
}

impl CrateDeclTokraRegion {
    pub fn data<'a>(self, db: &'a ::salsa::Db) -> CrateDeclTokraRegionDataRef<'a> {
        CrateDeclTokraRegionDataRef {
            ast_arena: self.ast_arena(db).as_arena_ref(),
            root_body: self.root_body(db),
            tokens_data: self.tokens_data(db),
            token_verse_starts: self.token_verse_starts(db),
        }
    }

    pub fn regional_tokens_data<'a>(self, db: &'a ::salsa::Db) -> RegionalTokensData<'a> {
        RegionalTokensData::new(self.tokens_data(db))
    }
}

pub trait HasCrateDeclTokraRegion {
    fn decl_tokra_region(self, db: &::salsa::Db) -> Option<CrateDeclTokraRegion>;
    fn decl_regional_token_idx_base(self, db: &::salsa::Db) -> Option<RegionalTokenIdxBase>;
}

impl HasCrateDeclTokraRegion for CratePath {
    fn decl_tokra_region(self, db: &::salsa::Db) -> Option<CrateDeclTokraRegion> {
        Some(crate_decl_tokra_region(db, self)?.0)
    }

    fn decl_regional_token_idx_base(self, db: &salsa::Db) -> Option<RegionalTokenIdxBase> {
        Some(
            crate_decl_tokra_region(db, self)?
                .1
                .regional_token_idx_base(db),
        )
    }
}

impl<'a> CrateDeclTokraRegionDataRef<'a> {
    pub fn root_body(self) -> CrateDeclAstIdxRange {
        self.root_body
    }

    pub fn token_stream(
        self,
        regional_token_verse_idx: RegionalTokenVerseIdx,
    ) -> RegionalTokenStream<'a> {
        debug_assert!(regional_token_verse_idx.lcurl().is_none());
        let regional_token_verse_start = self.token_verse_starts[regional_token_verse_idx.index()];
        let start_index = regional_token_verse_start.index();
        let end_index = self
            .token_verse_starts
            .get(regional_token_verse_idx.index() + 1)
            .map(|&end| end.index())
            .unwrap_or(self.tokens_data.len());
        RegionalTokenStream::new_crate_decl_regional_token_stream(
            &self.tokens_data[start_index..end_index],
            regional_token_verse_start,
        )
    }
}

#[salsa::tracked]
fn crate_decl_tokra_region(
    db: &::salsa::Db,
    crate_path: CratePath,
) -> Option<(CrateDeclTokraRegion, CrateDeclTokraRegionSourceMap)> {
    let builder = CrateDeclTokraRegionBuilder::new(crate_path, db)?;
    Some(builder.build())
}

struct CrateDeclTokraRegionBuilder<'a> {
    ast_sheet: &'a AstSheet,
    ast_token_idx_range_sheet: &'a AstTokenIdxRangeSheet,
    defn_ast_arena: CrateDeclAstArena,
    root_body: AstIdxRange,
    regional_token_verse_idx_base: RegionalTokenVerseIdxBase,
    regional_token_idx_base: RegionalTokenIdxBase,
    token_sheet_data: &'a TokenSheetData,
    ast_idx_map: Vec<AstIdx>,
    regional_token_idx_range_map: Vec<RegionalTokenIdxRange>,
    tokens_data: Vec<TokenData>,
    db: &'a ::salsa::Db,
}

impl<'a> CrateDeclTokraRegionBuilder<'a> {
    fn new(crate_path: CratePath, db: &'a ::salsa::Db) -> Option<Self> {
        let module_path = crate_path.root_module_path(db);
        let ast_sheet = module_path.ast_sheet(db);
        let top_level_asts = ast_sheet.top_level_asts();
        let mut top_level_asts_indexed_iter = ast_sheet.top_level_asts_indexed_iter();
        let (start, first_token_verse_idx) = loop {
            let (ast_idx, ast_data) = top_level_asts_indexed_iter.next()?;
            match *ast_data {
                AstData::Err {
                    token_verse_idx, ..
                }
                | AstData::BasicStmtOrBranch {
                    token_verse_idx, ..
                } => break (ast_idx, token_verse_idx),
                _ => return None,
            }
        };
        let end = loop {
            let Some((ast_idx, ast_data)) = top_level_asts_indexed_iter.next() else {
                break top_level_asts.end();
            };
            match *ast_data {
                AstData::Err { .. } | AstData::BasicStmtOrBranch { .. } => continue,
                _ => break ast_idx,
            }
        };
        let root_body = unsafe { AstIdxRange::new(start, end) };
        let regional_token_verse_idx_base =
            RegionalTokenVerseIdxBase::from_token_verse_idx(first_token_verse_idx);
        let ast_token_idx_range_sheet = module_path.ast_token_idx_range_sheet(db);
        let token_sheet_data = db.token_sheet_data(module_path);
        let token_idx_range: TokenIdxRange =
            ast_token_idx_range_sheet[start].join(ast_token_idx_range_sheet[root_body.end() - 1]);
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

    fn build(mut self) -> (CrateDeclTokraRegion, CrateDeclTokraRegionSourceMap) {
        let root_body = self.build_asts(self.root_body);
        let asts_token_idx_range = self
            .ast_token_idx_range_sheet
            .asts_token_idx_range(self.root_body);
        self.finish(root_body)
    }

    fn build_asts(&mut self, ast_idx_range: AstIdxRange) -> CrateDeclAstIdxRange {
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

    fn build_ast(&mut self, ast_idx: AstIdx) -> Option<CrateDeclAst> {
        match self.ast_sheet[ast_idx] {
            AstData::Err { .. } => Some(CrateDeclAst::Err),
            AstData::BasicStmtOrBranch {
                token_verse_idx,
                body,
            } => Some(CrateDeclAst::BasicStmtOrBranch {
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
            } => Some(CrateDeclAst::IfElseStmts {
                if_branch: self.build_ast_then_alloc(if_branch).expect("todo"),
                elif_branches: self.build_asts(elif_branches),
                else_branch: else_branch
                    .map(|else_branch| self.build_ast_then_alloc(else_branch).expect("todo")),
            }),
            AstData::MatchStmt {
                token_verse_idx,
                pattern_stmt,
                case_branches,
            } => Some(CrateDeclAst::MatchStmt {
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

    fn build_ast_then_alloc(&mut self, ast_idx: AstIdx) -> Option<CrateDeclAstIdx> {
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

    fn finish(
        self,
        root_body: CrateDeclAstIdxRange,
    ) -> (CrateDeclTokraRegion, CrateDeclTokraRegionSourceMap) {
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
            CrateDeclTokraRegion::new(
                self.db,
                self.tokens_data,
                self.defn_ast_arena,
                root_body,
                verse_starts,
                self.regional_token_idx_range_map,
            ),
            CrateDeclTokraRegionSourceMap::new(
                self.db,
                self.regional_token_verse_idx_base,
                self.regional_token_idx_base,
                self.ast_idx_map,
            ),
        )
    }
}
