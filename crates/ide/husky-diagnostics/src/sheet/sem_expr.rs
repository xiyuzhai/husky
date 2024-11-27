use super::*;
use husky_fly_term::*;
use husky_sem_expr::{
    OriginalSemExprDataError, OriginalSemExprTermError, OriginalSemExprTypeError, SemExprTermError,
};
use husky_syn_decl::decl::HasSynNodeDecl;
use husky_syn_defn::module_item_syn_node_defns;
use husky_syn_expr::region::SynExprRegion;
use salsa::DisplayWithDb;

#[salsa::tracked(db = DiagnosticsDb, jar = DiagnosticsJar)]
pub struct ExprTypeDiagnosticSheet {
    #[return_ref]
    pub diagnostics: Vec<Diagnostic>,
}

// TODO add diagnostics for htmx
#[salsa::tracked(jar = DiagnosticsJar)]
pub(crate) fn expr_ty_diagnostic_sheet(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> ExprTypeDiagnosticSheet {
    let mut diagnostics = vec![];
    for (syn_node_path, defn) in module_item_syn_node_defns(db, module_path) {
        let decl = syn_node_path.syn_node_decl(db);
        if let Some(syn_expr_region) = decl.syn_expr_region(db) {
            collect_expr_ty_diagnostics(db, syn_expr_region, &mut diagnostics);
        }
        if let Some(defn) = defn {
            collect_expr_ty_diagnostics(db, defn.syn_expr_region, &mut diagnostics);
        }
    }
    ExprTypeDiagnosticSheet::new(db, diagnostics)
}

fn collect_expr_ty_diagnostics(
    db: &::salsa::Db,
    syn_expr_region: SynExprRegion,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let ctx: RegionDiagnosticsContext = RegionDiagnosticsContext::new(db, syn_expr_region);
    let sem_expr_region_data = ctx.sem_expr_region_data();
    for (_expr_idx, fly_term_result) in sem_expr_region_data.sem_expr_terms().iter() {
        match fly_term_result {
            Err(SemExprTermError::Original(error)) => diagnostics.push(error.to_diagnostic(&ctx)),
            _ => (),
        }
    }
    for sem_expr_entry in sem_expr_region_data.sem_expr_arena().iter() {
        if let Some(e) = sem_expr_entry.original_data_error() {
            diagnostics.push(e.to_diagnostic(&ctx))
        }
        if let Some(e) = sem_expr_entry.original_data_error() {
            diagnostics.push(e.to_diagnostic(&ctx))
        }
    }
    let fly_term_region = sem_expr_region_data.fly_term_region();
    for (src, error) in fly_term_region.hollow_terms().errors() {
        diagnostics.push((src, error).to_diagnostic(&ctx))
    }
    for (src, error) in fly_term_region
        .expectations()
        .iter()
        .filter_map(|entry| Some((entry.src(), entry.original_error()?)))
    {
        diagnostics.push((src, error).to_diagnostic(&ctx))
    }
}

impl Diagnose for OriginalSemExprTermError {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, _db: &RegionDiagnosticsContext) -> String {
        match self {
            _ => todo!(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        todo!()
    }

    fn range(&self, _ctx: &RegionDiagnosticsContext) -> TextPositionRange {
        todo!()
    }
}

impl Diagnose for OriginalSemExprDataError {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, ctx: &RegionDiagnosticsContext) -> String {
        // MOM
        match self {
            OriginalSemExprDataError::NoSuchField {
                self_argument_ty: owner_ty,
                ident_token,
            } => {
                format!(
                    "Type Error: no field named {} in {}",
                    ident_token.ident().data(ctx.db()),
                    owner_ty.show2(ctx.db(), ctx.fly_term_region().terms())
                )
            }
            OriginalSemExprDataError::NoSuchMethod {
                self_expr_ty,
                ident_token,
            } => {
                format!(
                    "Type Error: no method named `{}` for type `{}`",
                    ident_token.ident().data(ctx.db()),
                    self_expr_ty.show2(ctx.db(), ctx.fly_term_region().terms()) // ad hoc
                )
            }
            OriginalSemExprDataError::ExpectedIndices => {
                format!("Type Error: expected indices")
            }
            OriginalSemExprDataError::CannotIndexIntoType { self_expr_ty } => {
                format!(
                    "Type Error: cannot index into type `{}`",
                    self_expr_ty.show2(ctx.db(), ctx.fly_term_region().terms())
                )
            }
            OriginalSemExprDataError::RitchieParameterArgumentMismatch {
                match_error: _,
                ritchie_arguments: _,
            } => todo!(), // OriginalSemExprDataError::UnexpectedArgument => {
                          //     format!("Type Error: unexpected argument")
                          // }
                          // OriginalSemExprDataError::MissingArgument => {
                          //     format!("Type Error: missing argument")
                          // }
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, _ctx: &RegionDiagnosticsContext) -> TextPositionRange {
        todo!()
        // match self {
        //     OriginalSemExprTypeError::NoSuchField { ident_token, .. } => {
        //         ctx.token_text_range(ident_token.regional_token_idx())
        //     }
        //     OriginalSemExprTypeError::NoMethodForType { ident_token, .. } => {
        //         ctx.token_text_range(ident_token.regional_token_idx())
        //     }
        //     _ => ctx.expr_text_range(self.0),
        // }
    }
}

impl Diagnose for OriginalSemExprTypeError {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, ctx: &RegionDiagnosticsContext) -> String {
        let db = ctx.db();
        match self {
            OriginalSemExprTypeError::UnresolvedTerm => {
                format!("Type Error: UnresolvedTerm")
            }
            OriginalSemExprTypeError::TypeMethodTypeError => format!("TypeError: "),
            OriginalSemExprTypeError::TypeCallTypeError => format!("TypeError: "),
            OriginalSemExprTypeError::TodoScopeResolution => {
                format!("Type Error: TodoScopeResolution")
            }
            OriginalSemExprTypeError::TodoBoxColon => {
                format!("Type Error: TodoBoxColon")
            }
            OriginalSemExprTypeError::FinalDestination => {
                format!("Type Error: final destination")
            }
            OriginalSemExprTypeError::FormPathTypeError => {
                format!("Type Error: form path error")
            }
            OriginalSemExprTypeError::AmbiguousTypePath => {
                format!("Type Error: AmbiguousTypePath")
            }
            OriginalSemExprTypeError::RitchieCallWrongNumberOfArguments {
                number_of_nonself_parameters,
                number_of_nonself_arguments,
            } => {
                format!("expected {number_of_nonself_parameters} argument, found {number_of_nonself_arguments}")
            }
            OriginalSemExprTypeError::AmbiguousListExpr => {
                format!("Type Error: AmbiguateListExpr")
            }
            OriginalSemExprTypeError::AmbiguousTildeExpr => {
                format!("Type Error: AmbiguateTildeExpr")
            }
            OriginalSemExprTypeError::ExpectedCurryButGotRitchieInstead => {
                format!("Type Error: expected curry but got Ritchie instead")
            }
            OriginalSemExprTypeError::CannotUnveil => {
                format!("Type Error: cannot unveil")
            }
            OriginalSemExprTypeError::CannotUnwrap => {
                format!("Type Error: cannot unwrap")
            }
            OriginalSemExprTypeError::NoConstructor { path } => {
                format!("Type Error: no constructor for `{}`", path.display(db))
            }
            OriginalSemExprTypeError::BitOperationOnlyWorksForRawBitsOrCustom => {
                format!("Type Error: no bit opr for integer")
            }
            OriginalSemExprTypeError::ExpectedNumTypeForIncrOrDecr => {
                format!("Type Error: ExpectedNumTypeForIncrOrDecr")
            }
            OriginalSemExprTypeError::ClosureParameterTypeNotInferred => {
                format!("Type Error: ClosureParameterTypeNotInferred")
            }
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, _ctx: &RegionDiagnosticsContext) -> TextPositionRange {
        todo!()
        // match self {
        //     OriginalSemExprTypeError::NoSuchField { ident_token, .. } => {
        //         ctx.token_text_range(ident_token.regional_token_idx())
        //     }
        //     OriginalSemExprTypeError::NoMethodForType { ident_token, .. } => {
        //         ctx.token_text_range(ident_token.regional_token_idx())
        //     }
        //     _ => ctx.expr_text_range(self.0),
        // }
    }
}

impl Diagnose for (HoleSource, &'_ OriginalHollowTermResolveError) {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, _db: &RegionDiagnosticsContext) -> String {
        match self.1 {
            OriginalHollowTermResolveError::UnresolvedTerm => "unresolved term".to_string(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, _ctx: &RegionDiagnosticsContext) -> TextPositionRange {
        match self.0 {
            HoleSource::Expr(_) => todo!(),
            HoleSource::Expectation(_) => todo!(),
            HoleSource::SemExpr(_) => todo!(),
            HoleSource::Pattern(_) => todo!(),
        }
    }
}

impl Diagnose for (ExpectationSource, &'_ OriginalFlyTermExpectationError) {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, ctx: &RegionDiagnosticsContext) -> String {
        match self.1 {
            OriginalFlyTermExpectationError::Todo => {
                format!("OriginalFlyTermExpectationError::Todo")
            }
            OriginalFlyTermExpectationError::TypePathMismatchForSubtyping {
                expected,
                expectee,
                expected_path,
                expectee_path,
            } => format!(
                "Type Error: type path mismatch in seeing `{}` as a subtype of `{}`, expected `{}`, but got `{}` instead",
                expectee.show2(ctx.db(), ctx.fly_term_region().terms()),
                expected.show2(ctx.db(), ctx.fly_term_region().terms()),
                expected_path.display(ctx.db()),
                expectee_path.display(ctx.db())
            ),
            OriginalFlyTermExpectationError::ExpectedCategory { expectee: _ } => {
                format!("Term Error: expected category",)
            }
            OriginalFlyTermExpectationError::ExpectedFunctionType => {
                format!("Term Error: expected function type",)
            }
            OriginalFlyTermExpectationError::ExpectedSubtype { expectee: _ } => {
                format!("Term Error: expected subtype",)
            }
            OriginalFlyTermExpectationError::ExpectedCoercion {  expectee, expected, contract } => {
                format!(
                    "Term Error: expected coercion from `{}` to `{}` under contract `{}`",
                    expectee.show2(ctx.db(), ctx.fly_term_region().terms()),
                    expected.show2(ctx.db(), ctx.fly_term_region().terms()),
                    contract.as_str(),
                )
            }
            OriginalFlyTermExpectationError::TypePathMismatchForCoercion { contract, ty_expected, expectee, expected_path, expectee_path } => format!(
                "Type Error: type path mismatch in coersing `{}` into `{}` of contract `{}`, expected `{}`, but got `{}` instead",
                expectee.show2(ctx.db(), ctx.fly_term_region().terms()),
                ty_expected.show2(ctx.db(), ctx.fly_term_region().terms()),
                contract.as_str(),
                expected_path.display(ctx.db()),
                expectee_path.display(ctx.db())
            ),
            OriginalFlyTermExpectationError::Place(e) => format!("place error {}", e),
            OriginalFlyTermExpectationError::ExpectedIntType {..} => todo!(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, ctx: &RegionDiagnosticsContext) -> TextPositionRange {
        ctx.expr_text_range(self.0.syn_expr_idx())
    }
}
