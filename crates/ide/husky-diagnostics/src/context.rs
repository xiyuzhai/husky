use crate::*;
use husky_ast::{AstSheet, HasAstSheet};
use husky_entity_tree::region_path::SynNodeRegionPath;
use husky_fly_term::FlyTermRegion;
use husky_regional_token::{RegionalTokenIdxBase, RegionalTokenIdxRange, RegionalTokenStreamState};
use husky_sem_expr::*;
use husky_syn_expr::{expr::SynExprIdx, range::SynExprRangeRegion, region::SynExprRegion};
use husky_token::{verse::idx::TokenVerseIdx, TokenDb, TokenIdx, TokenIdxRange, TokenStreamState};

pub(crate) struct SheetDiagnosticsContext<'a> {
    db: &'a ::salsa::Db,
    token_sheet_data: &'a TokenSheetData,
    ranged_token_sheet: &'a RangedTokenSheet,
    ast_sheet: &'a AstSheet,
}

impl<'a> SheetDiagnosticsContext<'a> {
    pub(crate) fn new(db: &'a ::salsa::Db, module_path: ModulePath) -> Self {
        let ranged_token_sheet = db.ranged_token_sheet(module_path);
        let token_sheet_data = ranged_token_sheet.token_sheet_data(db);
        Self {
            db,
            token_sheet_data,
            ranged_token_sheet,
            ast_sheet: module_path.ast_sheet(db),
        }
    }

    pub(crate) fn db(&self) -> &'a ::salsa::Db {
        self.db
    }

    pub(crate) fn token_sheet_data(&self) -> &TokenSheetData {
        self.token_sheet_data
    }

    pub(crate) fn token_idx_text_range(&self, token_idx: TokenIdx) -> TextPositionRange {
        self.ranged_token_sheet.token_text_range(token_idx)
    }

    pub(crate) fn token_stream_state_text_range(
        &self,
        token_stream_state: TokenStreamState,
    ) -> TextPositionRange {
        self.ranged_token_sheet
            .token_stream_state_text_range(token_stream_state)
    }

    pub(crate) fn token_verse_text_range(
        &self,
        token_verse_idx: TokenVerseIdx,
    ) -> TextPositionRange {
        let token_idx_range = self
            .token_sheet_data()
            .token_verse_token_idx_range(token_verse_idx);
        self.ranged_token_sheet.tokens_text_range(token_idx_range)
    }

    pub(crate) fn ast_sheet(&self) -> &'a AstSheet {
        self.ast_sheet
    }
}

pub(crate) struct RegionDiagnosticsContext<'a> {
    db: &'a ::salsa::Db,
    ranged_token_sheet: &'a RangedTokenSheet,
    sem_expr_region_data: &'a SemExprRegionData,
    expr_range_region: &'a SynExprRangeRegion,
    regional_token_idx_base: RegionalTokenIdxBase,
}

impl<'a> RegionDiagnosticsContext<'a> {
    pub(crate) fn new(db: &'a ::salsa::Db, syn_expr_region: SynExprRegion) -> Self {
        let syn_expr_region_data = &syn_expr_region.data(db);
        let module_path = syn_expr_region_data.path().module_path(db);
        let ranged_token_sheet = db.ranged_token_sheet(module_path);
        let sem_expr_region_data = db.sem_expr_region(syn_expr_region).data(db);
        let syn_expr_range_region = syn_expr_region.range_region(db);
        let regional_token_idx_base = match syn_expr_region_data.path() {
            SynNodeRegionPath::CrateDecl(_) => todo!(),
            SynNodeRegionPath::ItemDecl(path) => path.decl_regional_token_idx_base(db),
            SynNodeRegionPath::ItemDefn(path) => {
                path.defn_regional_token_idx_base(db).expect("todo")
            }
        };
        Self {
            db,
            ranged_token_sheet,
            sem_expr_region_data,
            expr_range_region: syn_expr_range_region,
            regional_token_idx_base,
        }
    }

    pub(crate) fn db(&self) -> &'a ::salsa::Db {
        self.db
    }

    pub(crate) fn sem_expr_region_data(&self) -> &SemExprRegionData {
        self.sem_expr_region_data
    }

    pub(crate) fn fly_term_region(&self) -> &FlyTermRegion {
        self.sem_expr_region_data.fly_term_region()
    }

    pub(crate) fn expr_text_range(&self, expr_idx: SynExprIdx) -> TextPositionRange {
        self.text_range(
            self.expr_range_region[expr_idx].token_idx_range(self.regional_token_idx_base),
        )
    }

    pub(crate) fn tokens_text_range(
        &self,
        regional_token_idx_range: RegionalTokenIdxRange,
    ) -> TextPositionRange {
        self.text_range(regional_token_idx_range.token_idx_range(self.regional_token_idx_base))
    }

    fn text_range(&self, token_idx_range: TokenIdxRange) -> TextPositionRange {
        assert!(token_idx_range.start().token_idx() < token_idx_range.end().token_idx());
        let first = self
            .ranged_token_sheet
            .token_text_range(token_idx_range.start().token_idx());
        let last = self
            .ranged_token_sheet
            .token_text_range(token_idx_range.end().token_idx() - 1);
        first.join(last)
    }

    pub(crate) fn token_stream_state_text_range(
        &self,
        regional_token_stream_state: RegionalTokenStreamState,
    ) -> TextPositionRange {
        self.ranged_token_sheet.token_stream_state_text_range(
            regional_token_stream_state.token_stream_state(self.regional_token_idx_base),
        )
    }
}
