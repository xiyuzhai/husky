use super::*;
use husky_syn_decl::decl::HasSynNodeDecl;
use husky_syn_defn::{module_item_syn_node_defns, ItemSynNodeDefn};
use husky_syn_expr::{
    entity_path::SynPrincipalEntityPathExpr,
    error::{OriginalSynExprError, SynExprError, SynExprResult},
    expr::SynExprData,
    region::SynExprRegion,
    stmt::SynStmtData,
};

#[salsa::tracked(db = DiagnosticsDb, jar = DiagnosticsJar)]
pub struct ExprDiagnosticSheet {
    #[return_ref]
    pub diagnostics: Vec<Diagnostic>,
}

#[salsa::tracked(jar = DiagnosticsJar)]
pub(crate) fn expr_diagnostic_sheet(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> ExprDiagnosticSheet {
    let mut sheet_collector = ModuleDiagnosticsCollector::new(db, module_path);
    for (syn_node_path, defn) in module_item_syn_node_defns(db, module_path) {
        let decl = syn_node_path.syn_node_decl(db);
        if let Some(syn_expr_region) = decl.syn_expr_region(db) {
            sheet_collector
                .region_collector(syn_expr_region)
                .collect_expr_diagnostics(syn_expr_region);
        }
        if let Some(ItemSynNodeDefn {
            syn_expr_region, ..
        }) = defn
        {
            sheet_collector
                .region_collector(syn_expr_region)
                .collect_expr_diagnostics(syn_expr_region);
        }
    }
    let diagnostics = sheet_collector.finish();
    ExprDiagnosticSheet::new(db, diagnostics)
}

impl<'a, 'b> RegionDiagnosticsCollector<'a, 'b> {
    fn visit_syn_expr_result<T>(&mut self, result: &SynExprResult<T>) {
        if let Err(SynExprError::Original(e)) = result {
            self.visit_atom(e)
        }
    }
    fn collect_expr_diagnostics(&mut self, syn_expr_region: SynExprRegion) {
        let expr_region_data = syn_expr_region.data(self.db());
        for expr in expr_region_data.expr_arena().data() {
            match expr {
                SynExprData::Err(SynExprError::Original(e)) => self.visit_atom(e),
                // self.visit_atom(e),
                _ => (),
            }
        }
        for stmt in expr_region_data.stmt_arena().data() {
            match stmt {
                SynStmtData::Let {
                    let_token: _,
                    let_variables_pattern,
                    assign_token,
                    initial_value: _,
                } => {
                    self.visit_syn_expr_result(let_variables_pattern);
                    self.visit_syn_expr_result(assign_token);
                }
                SynStmtData::Return {
                    return_token: _,
                    result: _,
                } => {}
                SynStmtData::Require {
                    require_token: _,
                    condition: _,
                } => {}
                SynStmtData::Assert {
                    assert_token: _,
                    condition: _,
                } => {}
                SynStmtData::Break { break_token: _ } => {}
                SynStmtData::Eval { .. } => {}
                SynStmtData::ForBetween {
                    particulars,
                    eol_colon,
                    ..
                } => {
                    self.visit_syn_expr_result(&particulars.range);
                    self.visit_syn_expr_result(eol_colon);
                }
                SynStmtData::ForIn {
                    for_token: _,
                    condition: _,
                    eol_colon: _,
                    block: _,
                } => todo!(),
                SynStmtData::ForExt {
                    forext_token: _,
                    particulars: _,
                    eol_colon,
                    block: _,
                } => {
                    self.visit_syn_expr_result(eol_colon);
                    // todo: handle errors in particulars
                }
                SynStmtData::While {
                    while_token: _,
                    condition,
                    eol_colon,
                    block: _,
                } => {
                    self.visit_syn_expr_result(condition);
                    self.visit_syn_expr_result(eol_colon);
                }
                SynStmtData::DoWhile {
                    do_token: _,
                    while_token: _,
                    condition,
                    eol_colon,
                    block: _,
                } => {
                    self.visit_syn_expr_result(condition);
                    self.visit_syn_expr_result(eol_colon);
                }
                SynStmtData::IfElse {
                    if_branch,
                    elif_branches,
                    else_branch,
                } => {
                    self.visit_syn_expr_result(&if_branch.condition);
                    self.visit_syn_expr_result(&if_branch.eol_colon);
                    for elif_branch in elif_branches {
                        self.visit_syn_expr_result(&elif_branch.condition);
                        self.visit_syn_expr_result(&elif_branch.eol_colon);
                    }
                    if let Some(else_branch) = else_branch {
                        self.visit_syn_expr_result(&else_branch.eol_colon_token);
                    }
                }
                SynStmtData::Match {
                    match_token: _,
                    match_expr,
                    eol_with_token,
                    ref case_branches,
                } => {
                    self.visit_syn_expr_result(match_expr);
                    self.visit_syn_expr_result(eol_with_token);
                    for case_branch in case_branches {
                        self.visit_syn_expr_result(&case_branch.case_pattern_syn_obelisk);
                        self.visit_syn_expr_result(&case_branch.heavy_arrow_token);
                        self.visit_syn_expr_result(&case_branch.stmts);
                    }
                }
                // ad hoc
                SynStmtData::Narrate { narrate_token } => (),
            }
        }
        for item_path_expr in expr_region_data.principal_item_path_expr_arena().data() {
            match item_path_expr {
                SynPrincipalEntityPathExpr::Root { .. } => (),
                SynPrincipalEntityPathExpr::Subitem {
                    ident_token, path, ..
                } => {
                    match ident_token {
                        Err(SynExprError::Original(e)) => self.visit_atom(e),
                        _ => (),
                    }
                    match path {
                        Err(SynExprError::Original(e)) => self.visit_atom(e),
                        _ => (),
                    }
                }
            }
        }
    }
}

impl Diagnose for OriginalSynExprError {
    type Context<'a> = RegionDiagnosticsContext<'a>;

    fn message(&self, _db: &Self::Context<'_>) -> String {
        match self {
            OriginalSynExprError::MismatchingDelimiter { .. } => {
                format!("Syntax Error: mismatching bracket")
            }
            OriginalSynExprError::ExpectedRightAngleDelimiter { .. } => {
                format!("Syntax Error: expected `>`")
            }
            OriginalSynExprError::ExpectedRightCurlyBrace(_) => {
                format!("Syntax Error: expected `}}`")
            }
            OriginalSynExprError::ExpectedIdent(_) => format!("Syntax Error: expected identifier"),
            OriginalSynExprError::ExpectedColon(_) => format!("Syntax Error: expected `:`"),
            OriginalSynExprError::ExpectedRpar(_) => {
                format!("Syntax Error: expected `)`")
            }
            OriginalSynExprError::NoMatchingBra { .. } => {
                format!("Syntax Error: no matching bracket")
            }
            OriginalSynExprError::ExpectedIdentAfterDot { .. } => {
                format!("Syntax Error: expected identifier after dot")
            }
            OriginalSynExprError::NoLeftOperandForBinaryOperator { .. } => {
                format!("Syntax Error: no left operand for binary operator")
            }
            OriginalSynExprError::NoRightOperandForBinaryOperator { .. } => {
                format!("Syntax Error: no right operand for binary operator")
            }
            OriginalSynExprError::NoOperandForPrefixOperator { .. } => {
                format!("Syntax Error:no operand for prefix operator")
            }
            OriginalSynExprError::ExpectedItemBeforeComma { .. } => {
                format!("Syntax Error: expected item before `,`")
            }
            OriginalSynExprError::ExpectedItemBeforeBe { .. } => {
                format!("Syntax Error: expected item before `be`")
            }
            OriginalSynExprError::ExpectedLetPattern(_) => {
                format!("Syntax Error: expected variable pattern after `let`")
            }
            OriginalSynExprError::ExpectedBePattern(_) => {
                format!("Syntax Error: expected pattern after `be`")
            }
            OriginalSynExprError::ExpectedCasePattern(_) => {
                format!("Syntax Error: expected pattern after `|`")
            }
            OriginalSynExprError::ExpectedAssign(_) => format!("Syntax Error: expected `=`"),
            OriginalSynExprError::ExpectedInitialValue(_) => {
                format!("Syntax Error: expected initial value")
            }
            OriginalSynExprError::UnexpectedKeyword(_) => {
                format!("Syntax Error: unexpected keyword")
            }
            OriginalSynExprError::ExpectedResult(_) => format!("Syntax Error: expected result"),
            OriginalSynExprError::ExpectedCondition(_) => {
                format!("Syntax Error: expected condition")
            }
            OriginalSynExprError::ExpectedMatchExpr(_) => {
                format!("Syntax Error: expected match expression")
            }
            OriginalSynExprError::ExpectedEolWithInMatchHead(_) => {
                format!("Syntax Error: expected end of line `with` in match head")
            }
            OriginalSynExprError::ExpectedForExpr(_) => format!("Syntax Error: expected for expr"),
            OriginalSynExprError::ExpectedParameterPattern(_) => {
                format!("Syntax Error: expected paramter pattern")
            }
            OriginalSynExprError::ExpectedEolColon(_) => {
                format!("Syntax Error: expected `:` at end of line")
            }
            OriginalSynExprError::ExpectedIdentAfterModifier(_, _) => {
                format!("Syntax Error: expected identifier after `mut`")
            }
            OriginalSynExprError::ExpectedConstantImplicitParameterType(_) => {
                format!("Syntax Error: expected constant implicit parameter type")
            }
            OriginalSynExprError::ExpectedHeavyArrowAfterCasePattern(_token_stream_state) => {
                format!("Syntax Error: expected `=>` after case pattern")
            }
            OriginalSynExprError::ExpectedBlock(_) => format!("Syntax Error: expected block"),
            OriginalSynExprError::UnterminatedList { .. } => {
                format!("Syntax Error: unterminated list")
            }
            OriginalSynExprError::UnterminatedFunctionCallKeyedArgumentList {
                bra_regional_token_idx: _,
            } => {
                format!("Syntax Error: unterminated function call keyed argument list")
            }
            OriginalSynExprError::UnterminatedMethodCallKeyedArgumentList {
                bra_regional_token_idx: _,
            } => {
                format!("Syntax Error: unterminated method call keyed argument list")
            }
            OriginalSynExprError::UnexpectedSheba(_) => format!("Syntax Error: unexpected `$`"),
            OriginalSynExprError::UnrecognizedIdent {
                regional_token_idx: _,
                ident: _,
            } => {
                format!("Syntax Error: unrecognized identifier")
            }
            OriginalSynExprError::ExpectedLetVariablesType(_) => {
                format!("Syntax Error: expected let variables type")
            }
            OriginalSynExprError::ExpectedFieldType(_) => {
                format!("Syntax Error: expected field type")
            }
            OriginalSynExprError::ExpectedParameterType(_) => {
                format!("Syntax Error: expected parameter type")
            }
            OriginalSynExprError::SelfTypeNotAllowed(_) => {
                format!("Syntax Error: SelfTypeNotAllowed")
            }
            OriginalSynExprError::SelfValueNotAllowed(_) => {
                format!("Syntax Error: SelfValueNotAllowed")
            }
            OriginalSynExprError::ExpectedExprBeforeDot { .. } => {
                format!("Syntax Error: ExpectedExprBeforeDot")
            }
            OriginalSynExprError::HtmlTodo(_) => {
                format!("Syntax Error: HtmlTodo")
            }
            OriginalSynExprError::ExpectedValueForFieldBindInitialization(_) => {
                format!("Syntax Error: ExpectedValueForFieldBindInitialization")
            }
            OriginalSynExprError::ExpectedFunctionIdentAfterOpeningHtmlBra(_) => {
                format!("Syntax Error: ExpectedFunctionIdentAfterOpeningHtmlBra")
            }
            OriginalSynExprError::UnexpectedInlineLcurl(_) => {
                format!("Syntax Error: UnexpectedLeftCurlyBrace")
            }
            OriginalSynExprError::ExpectedTraits(_) => todo!(),
            OriginalSynExprError::ExpectedTypeAfterLightArrow {
                light_arrow_token: _,
            } => todo!(),
            OriginalSynExprError::ExpectedExplicitParameterDefaultValue(_) => todo!(),
            OriginalSynExprError::ExpectedTypeTermForAssocType(_) => {
                format!("Syntax Error: ExpectedTypeTermForAssocType")
            }
            OriginalSynExprError::ExpectIdentAfterScopeResolution(_) => todo!(),
            OriginalSynExprError::EntityTree {
                regional_token_idx: _,
                error: _,
            } => todo!(),
            OriginalSynExprError::ExpectedBlockRcurl(_) => todo!(),
            OriginalSynExprError::ExpectedRvertForClosure(_) => todo!(),
            OriginalSynExprError::ExpectedEqTokenAfterReturnTypeForClosure(_) => todo!(),
            OriginalSynExprError::ExpectedReturnTypeAfterLightArrowForClosure(_) => todo!(),
            OriginalSynExprError::ExpectedBodyExprForClosure(_) => todo!(),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, ctx: &Self::Context<'_>) -> TextPositionRange {
        ctx.tokens_text_range(self.regional_token_idx_range())
    }
}
