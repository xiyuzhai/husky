use super::*;
use husky_ast::AstData;
use husky_entity_tree::{
    error::EntityTreeError,
    error::OriginalEntityTreeError,
    expr::module_item_path::{MajorPathExprError, OriginalMajorItemPathExprError},
    jar::EntityTreeDb,
    node::impl_block::ill_formed_impl_block::ImplBlockIllForm,
};

#[salsa::tracked(db = DiagnosticsDb, jar = DiagnosticsJar)]
pub struct EntityTreeDiagnosticSheet {
    #[return_ref]
    pub diagnostics: Vec<Diagnostic>,
}

#[salsa::tracked(jar = DiagnosticsJar)]
pub(crate) fn item_tree_diagnostic_sheet(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> EntityTreeDiagnosticSheet {
    let mut diagnostics = vec![];
    let ctx = SheetDiagnosticsContext::new(db, module_path);
    let item_syn_tree_sheet = db.item_syn_tree_sheet(module_path);
    for e in item_syn_tree_sheet.errors() {
        match e {
            EntityTreeError::Original(e) => diagnostics.push(e.to_diagnostic(&ctx)),
            EntityTreeError::Derived(_) => (),
        }
    }
    for impl_block_ill_form in item_syn_tree_sheet.all_impl_block_ill_forms(db) {
        diagnostics.push(impl_block_ill_form.to_diagnostic(&ctx))
    }
    // todo
    EntityTreeDiagnosticSheet::new(db, diagnostics)
}

impl Diagnose for OriginalEntityTreeError {
    type Context<'a> = SheetDiagnosticsContext<'a>;

    fn message(&self, _db: &Self::Context<'_>) -> String {
        match self {
            OriginalEntityTreeError::UnresolvedRootIdent(_) => format!("unresolved identifier"),
            OriginalEntityTreeError::NoVisibleSubitem => format!("NoSubitem"),
            OriginalEntityTreeError::EntitySymbolAlreadyDefined { old: _, new: _ } => {
                format!("EntitySymbolAlreadyDefined")
            }
            OriginalEntityTreeError::ExpectIdentAfterKeyword => {
                format!("ExpectIdentAfterKeyword")
            }
            OriginalEntityTreeError::InvalidTypePath(_) => todo!(),
            OriginalEntityTreeError::CanOnlyUseParentSuperForModulePath => todo!(),
            OriginalEntityTreeError::NoSuperForCrateRoot { super_token: _ } => todo!(),
            OriginalEntityTreeError::NoSubitemForForm => todo!(),
            OriginalEntityTreeError::InvalidParentPath {
                name_token: _,
                principal_entity_path: _,
            } => todo!(),
            OriginalEntityTreeError::StandaloneSelf => todo!(),
            OriginalEntityTreeError::SameNameTypeItemsButNotTheSameKind => todo!(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, ctx: &Self::Context<'_>) -> TextPositionRange {
        let db = ctx.db();
        match self {
            OriginalEntityTreeError::UnresolvedRootIdent(ident_token) => {
                ctx.token_idx_text_range(ident_token.token_idx())
            }
            OriginalEntityTreeError::NoVisibleSubitem => todo!(),
            OriginalEntityTreeError::EntitySymbolAlreadyDefined { old: _, new } => {
                match ctx.ast_sheet()[new.decl_ast_idx(db)] {
                    AstData::Use {
                        token_verse_idx: _,
                        visibility_expr: _,
                        state_after_visibility_expr: _,
                    } => todo!(),
                    AstData::Identifiable { ident_token, .. }
                    | AstData::TypeVariant { ident_token, .. } => {
                        ctx.token_idx_text_range(ident_token.token_idx())
                    }
                    _ => unreachable!(),
                }
            }
            OriginalEntityTreeError::ExpectIdentAfterKeyword => todo!(),
            OriginalEntityTreeError::InvalidTypePath(_) => todo!(),
            OriginalEntityTreeError::CanOnlyUseParentSuperForModulePath => todo!(),
            OriginalEntityTreeError::NoSuperForCrateRoot { super_token: _ } => todo!(),
            OriginalEntityTreeError::NoSubitemForForm => todo!(),
            OriginalEntityTreeError::InvalidParentPath {
                name_token: _,
                principal_entity_path: _,
            } => todo!(),
            OriginalEntityTreeError::StandaloneSelf => todo!(),
            OriginalEntityTreeError::SameNameTypeItemsButNotTheSameKind => todo!(),
        }
    }
}

impl Diagnose for ImplBlockIllForm {
    type Context<'a> = SheetDiagnosticsContext<'a>;

    fn message(&self, ctx: &Self::Context<'_>) -> String {
        match self {
            ImplBlockIllForm::UnmatchedAngleBras => todo!(),
            ImplBlockIllForm::TokenData(_) => todo!(),
            ImplBlockIllForm::MajorPath(e) => match e {
                MajorPathExprError::Original(e) => match e {
                    OriginalMajorItemPathExprError::UnrecognizedIdent(ident_token) => {
                        format!(
                            "Syntax Error: unrecognized identifier `{}` for major entity path",
                            ident_token.ident().data(ctx.db())
                        )
                    }
                    OriginalMajorItemPathExprError::ExpectedName(_) => {
                        format!("expected identifier",)
                    }
                    OriginalMajorItemPathExprError::NoSuchSubitem => todo!(),
                    OriginalMajorItemPathExprError::NoSuperForCrateRoot { super_token: _ } => {
                        todo!()
                    }
                    OriginalMajorItemPathExprError::PathIsNotMajor {
                        ident_token: _,
                        path: _,
                    } => todo!(),
                    OriginalMajorItemPathExprError::NoSuperForParent {
                        parent: _,
                        super_token: _,
                    } => todo!(),
                    OriginalMajorItemPathExprError::ExpectedMajorItemButGotModule {
                        name_token: _,
                        module_path: _,
                    } => todo!(),
                    OriginalMajorItemPathExprError::NoColonColonAfterMajorItemPath => todo!(),
                },
                MajorPathExprError::Derived(_) => todo!(),
            },
            ImplBlockIllForm::MissingForKeyword => format!("missing `for` keyword"),
            ImplBlockIllForm::ExpectTypePathAfterForKeyword => {
                format!("expect type path after `for` keyword")
            }
            ImplBlockIllForm::ExpectedDeriveIdent(_) => todo!(),
            ImplBlockIllForm::UnexpectedFormPath(_) => todo!(),
            ImplBlockIllForm::InvalidTypeSketch => todo!(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, ctx: &Self::Context<'_>) -> TextPositionRange {
        match self {
            ImplBlockIllForm::UnmatchedAngleBras => todo!(),
            ImplBlockIllForm::TokenData(_) => todo!(),
            ImplBlockIllForm::MajorPath(e) => match e {
                MajorPathExprError::Original(e) => match e {
                    OriginalMajorItemPathExprError::UnrecognizedIdent(ident_token)
                    | OriginalMajorItemPathExprError::PathIsNotMajor { ident_token, .. } => {
                        ctx.token_idx_text_range(ident_token.token_idx())
                    }
                    OriginalMajorItemPathExprError::ExpectedName(token_stream_state) => {
                        match token_stream_state.drained() {
                            true => todo!(),
                            false => ctx.token_idx_text_range(token_stream_state.next_token_idx()),
                        }
                    }
                    OriginalMajorItemPathExprError::NoSuchSubitem => todo!(),
                    OriginalMajorItemPathExprError::NoSuperForCrateRoot { super_token } => {
                        ctx.token_idx_text_range(super_token.token_idx())
                    }
                    OriginalMajorItemPathExprError::NoSuperForParent {
                        parent: _,
                        super_token: _,
                    } => todo!(),
                    OriginalMajorItemPathExprError::ExpectedMajorItemButGotModule {
                        name_token: _,
                        module_path: _,
                    } => todo!(),
                    OriginalMajorItemPathExprError::NoColonColonAfterMajorItemPath => todo!(),
                },
                MajorPathExprError::Derived(_) => todo!(),
            },
            ImplBlockIllForm::MissingForKeyword => todo!(),
            ImplBlockIllForm::ExpectTypePathAfterForKeyword => todo!(),
            ImplBlockIllForm::ExpectedDeriveIdent(_) => todo!(),
            ImplBlockIllForm::UnexpectedFormPath(_) => todo!(),
            ImplBlockIllForm::InvalidTypeSketch => todo!(),
        }
    }
}
