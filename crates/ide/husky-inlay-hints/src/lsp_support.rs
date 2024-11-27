use crate::*;
use crate_decl::crate_decl_inlay_hints;
use husky_entity_path::{path::ItemPath, region::RegionPath};
use husky_entity_tree::helpers::{paths::module_item_paths, tokra_region::HasRegionalTokenIdxBase};
use husky_regional_token::RegionalTokenIdxBase;
use husky_text::Text;
use husky_token::{sheet::RangedTokenSheet, TokenDb};
use husky_vfs::path::{crate_path::CratePath, module_path::ModulePathData};
use item_decl::item_decl_inlay_hints;
use item_defn::item_defn_inlay_hints;

#[sealed::sealed]
pub trait HasLspInlayHints: Is<ModulePath> + Copy {
    fn lsp_inlay_hints(
        self,
        db: &::salsa::Db,
        range: Option<TextPositionRange>,
    ) -> InlayHintResult<Option<Vec<lsp_types::InlayHint>>>;
}

#[sealed::sealed]
impl HasLspInlayHints for ModulePath {
    fn lsp_inlay_hints(
        self,
        db: &salsa::Db,
        range: Option<TextPositionRange>,
    ) -> InlayHintResult<Option<Vec<lsp_types::InlayHint>>> {
        let mut builder = LspInlayHintBuilder::new(self, range, db);
        match self.data(db) {
            ModulePathData::Root(crate_path) => builder.add_crate_decl(crate_path),
            ModulePathData::Child { parent, ident } => (),
            ModulePathData::Script { script } => (),
        }
        for &item_path in module_item_paths(db, self) {
            builder.add_item_decl_and_defn(item_path)
        }
        Ok(Some(builder.finish()))
    }
}

#[test]
fn module_lsp_inlay_hints_works() {
    DB::ast_rich_test_debug(
        |db, module_path: ModulePath| module_path.lsp_inlay_hints(db, None),
        &AstTestConfig::new(
            "module_lsp_inlay_hints",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::IDE,
        ),
    )
}

struct LspInlayHintBuilder<'db> {
    db: &'db ::salsa::Db,
    text_range: Option<TextPositionRange>,
    base: Option<RegionalTokenIdxBase>,
    token_range_sheet_data: &'db RangedTokenSheet,
    lsp_inlay_hints: Vec<lsp_types::InlayHint>,
}

impl<'db> LspInlayHintBuilder<'db> {
    fn new(
        module_path: ModulePath,
        range: Option<TextPositionRange>,
        db: &'db ::salsa::Db,
    ) -> Self {
        Self {
            db,
            text_range: range,
            base: None,
            token_range_sheet_data: db.ranged_token_sheet(module_path),
            lsp_inlay_hints: vec![],
        }
    }
}

impl<'db> LspInlayHintBuilder<'db> {
    #[track_caller]
    fn base(&self) -> RegionalTokenIdxBase {
        self.base.unwrap()
    }
}

/// # actions
impl<'db> LspInlayHintBuilder<'db> {
    fn add_crate_decl(&mut self, crate_path: CratePath) {
        let db = self.db;
        self.add_inlay_hints_in_region(
            RegionPath::CrateDecl(crate_path).regional_token_idx_base(db),
            crate_decl_inlay_hints(db, crate_path),
        );
    }

    fn add_item_decl_and_defn(&mut self, item_path: ItemPath) {
        let db = self.db;
        self.add_inlay_hints_in_region(
            RegionPath::ItemDecl(item_path).regional_token_idx_base(db),
            item_decl_inlay_hints(db, *item_path),
        );
        self.add_inlay_hints_in_region(
            RegionPath::ItemDefn(item_path).regional_token_idx_base(db),
            item_defn_inlay_hints(db, *item_path),
        );
    }

    fn add_inlay_hints_in_region(
        &mut self,
        base: Option<RegionalTokenIdxBase>,
        inlay_hints: &'db [InlayHint],
    ) {
        let Some(base) = base else { return };
        self.with_base(base, |slf| {
            if let Some(text_range) = slf.text_range {
                if !slf
                    .token_range_sheet_data
                    .tokens_text_range(base.token_idx_range())
                    .intersects(text_range)
                {
                    return;
                }
            }
            slf.add_inlay_hints(inlay_hints);
        });
    }
    fn with_base(&mut self, base: RegionalTokenIdxBase, f: impl FnOnce(&mut Self)) {
        debug_assert!(self.base.is_none());
        self.base = Some(base);
        f(self);
        self.base = None;
    }

    fn add_inlay_hints(&mut self, inlay_hints: &'db [InlayHint]) {
        for inlay_hint in inlay_hints {
            if let Some(lsp_inlay_hint) = inlay_hint.lsp(self) {
                self.lsp_inlay_hints.push(lsp_inlay_hint)
            }
        }
    }

    fn finish(self) -> Vec<lsp_types::InlayHint> {
        self.lsp_inlay_hints
    }
}

impl InlayHint {
    fn lsp(&self, builder: &LspInlayHintBuilder) -> Option<lsp_types::InlayHint> {
        let text_position = match self.position {
            InlayHintPosition::EndOfRegionSpaced => builder
                .token_range_sheet_data
                .tokens_text_range(builder.base().token_idx_range())
                .end
                .to_right(1),
        };
        if let Some(text_range) = builder.text_range {
            if !(text_range.start < text_position && text_position < text_range.end) {
                return None;
            }
        }
        Some(lsp_types::InlayHint {
            position: text_position.into(),
            label: self.label.lsp(),
            kind: self.kind.into(),
            text_edits: None,
            tooltip: None,
            padding_left: Some(true),
            padding_right: None,
            data: None,
        })
    }
}

impl Into<Option<lsp_types::InlayHintKind>> for InlayHintKind {
    fn into(self) -> Option<lsp_types::InlayHintKind> {
        match self {
            InlayHintKind::TypeAnnotation => Some(lsp_types::InlayHintKind::TYPE),
            InlayHintKind::ParameterIdent => Some(lsp_types::InlayHintKind::PARAMETER),
            InlayHintKind::AttrInferred => None,
        }
    }
}

impl InlayHintLabel {
    fn lsp(&self) -> lsp_types::InlayHintLabel {
        match self {
            InlayHintLabel::String(label) => lsp_types::InlayHintLabel::String(label.clone()),
            InlayHintLabel::LabelParts(parts) => lsp_types::InlayHintLabel::LabelParts(todo!()),
        }
    }
}
