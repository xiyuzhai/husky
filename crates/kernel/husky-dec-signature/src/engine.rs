mod pattern_ty;

pub(crate) use self::pattern_ty::*;

use crate::*;
use husky_entity_path::path::{major_item::MajorItemPath, PrincipalEntityPath};
use husky_entity_tree::region_path::SynNodeRegionPath;
use husky_print_utils::p;
use husky_syn_expr::{
    context::SynExprRootKind,
    expr::{SynExprData, SynExprIdx, SynExprMap},
    pattern::{ParenateParameterSynPatternRoot, SynPatternMap, SynPatternSymbolMap},
    region::{SynExprRegion, SynExprRegionData},
    variable::{
        CurrentTemplateVariableData, CurrentVariableData, CurrentVariableIdx,
        CurrentVariableIdxRange, SyndicateTypeConstraint, TemplateSymbolSynAttr,
    },
};
use husky_syn_opr::{SynBinaryOpr, SynPrefixOpr};
use husky_vfs::toolchain::Toolchain;
use salsa::DebugWithDb;
use ty_as_trai::DecTypeAsTrait;

pub(super) struct DecTermEngine<'a> {
    db: &'a ::salsa::Db,
    toolchain: Toolchain,
    syn_expr_region_data: &'a SynExprRegionData,
    dec_term_menu: &'a DecTermMenu,
    symbolic_variable_region: DecSymbolicVariableRegion,
    expr_terms: SynExprMap<SynExprDecTermResult<DecTerm>>,
    /// todo: change this to ordered
    pattern_ty_infos: SynPatternMap<PatternDeclarativeTypeInfo>,
    pattern_variable_ty_infos: SynPatternSymbolMap<DecPatternVariableTypeInfo>,
}

/// returns None for defn region
#[salsa::tracked(return_ref)]
pub fn syn_expr_dec_term_region(
    db: &::salsa::Db,
    syn_expr_region: SynExprRegion,
) -> SynExprDecTermRegion {
    let expr_region_data = syn_expr_region.data(db);
    let parent_expr_region = expr_region_data.parent();
    let parent_term_symbol_region =
        parent_expr_region.map(|r| syn_expr_dec_term_region(db, r).symbolic_variable_region());
    let engine = DecTermEngine::new(db, syn_expr_region, parent_term_symbol_region);
    engine.infer_all()
}

impl<'a> DecTermEngine<'a> {
    fn new(
        db: &'a ::salsa::Db,
        syn_expr_region: SynExprRegion,
        parent_term_symbol_region: Option<&'a DecSymbolicVariableRegion>,
    ) -> Self {
        let toolchain = syn_expr_region.toolchain(db);
        let dec_term_menu = db.dec_term_menu(toolchain).unwrap();
        let syn_expr_region_data = &syn_expr_region.data(db);
        Self {
            db,
            toolchain,
            syn_expr_region_data,
            dec_term_menu,
            symbolic_variable_region: DecSymbolicVariableRegion::new(
                parent_term_symbol_region,
                syn_expr_region_data,
                dec_term_menu,
            ),
            expr_terms: SynExprMap::new(syn_expr_region_data.expr_arena()),
            pattern_ty_infos: SynPatternMap::new(syn_expr_region_data.pattern_arena()),
            pattern_variable_ty_infos: SynPatternSymbolMap::new(
                syn_expr_region_data
                    .pattern_region()
                    .pattern_variable_arena(),
            ),
        }
    }

    pub(crate) fn path(&self) -> SynNodeRegionPath {
        self.syn_expr_region_data.path()
    }

    fn infer_all(mut self) -> SynExprDecTermRegion {
        // ad hoc, todo: make it clear what it means for defn and snippet region
        match self.path() {
            SynNodeRegionPath::CrateDecl(_) => self.infer_expr_roots(),
            SynNodeRegionPath::ItemDecl(_) => {
                self.infer_current_svar_terms();
                self.symbolic_variable_region
                    .infer_self_ty_parameter_and_self_value_parameter(
                        self.db,
                        self.toolchain,
                        self.syn_expr_region_data.path(),
                        self.syn_expr_region_data.variable_region(),
                    );
                self.infer_expr_roots();
            }
            SynNodeRegionPath::ItemDefn(_) => (),
        };
        self.finish()
    }

    fn infer_current_svar_terms(&mut self) {
        let mut current_svar_indexed_iter = self
            .syn_expr_region_data
            .variable_region()
            .indexed_current_variables();
        for (pattern_ty_constraint, vars) in self
            .syn_expr_region_data
            .variable_region()
            .pattern_ty_constraints()
        {
            match pattern_ty_constraint {
                SyndicateTypeConstraint::TemplateTypeParameter => {
                    let (current_variable_idx, current_variable) = current_svar_indexed_iter
                        .next()
                        .expect("ty constraint should match with current symbols");
                    let CurrentVariableData::TemplateParameter {
                        syn_attrs,
                        annotated_variance_token,
                        data: template_parameter_variant,
                    } = current_variable.data()
                    else {
                        unreachable!()
                    };
                    let attrs = DeclarativeTemplateVariableAttrs::from_attrs(syn_attrs.iter().map(
                        |syn_attr| match syn_attr {
                            TemplateSymbolSynAttr::Phantom(_, _) => {
                                DeclarativeTemplateSymbolAttr::Phan
                            }
                            TemplateSymbolSynAttr::Runtime(_, _) => {
                                DeclarativeTemplateSymbolAttr::Poly
                            }
                        },
                    ));
                    let variance = annotated_variance_token.map(|vt| vt.into());
                    let (name, (ty, term_symbol), trai_expr_idxs): (_, _, &[SynExprIdx]) =
                        match *template_parameter_variant {
                            CurrentTemplateVariableData::Lifetime { label_token } => (
                                label_token.label().into(),
                                DecSymbolicVariable::new_lifetime(
                                    self.db,
                                    self.toolchain,
                                    self.dec_term_menu,
                                    &mut self.symbolic_variable_region.registry_mut(),
                                    attrs,
                                    variance,
                                ),
                                &[], // ad hoc
                            ),
                            CurrentTemplateVariableData::Place { label_token } => (
                                label_token.label().into(),
                                DecSymbolicVariable::new_place(
                                    self.db,
                                    self.toolchain,
                                    self.dec_term_menu,
                                    &mut self.symbolic_variable_region.registry_mut(),
                                    attrs,
                                    variance,
                                ),
                                &[], // ad hoc
                            ),
                            CurrentTemplateVariableData::Type {
                                ident_token,
                                ref trai_syn_expr_idxs,
                            } => (
                                ident_token.ident().into(),
                                DecSymbolicVariable::new_ty(
                                    self.db,
                                    self.toolchain,
                                    self.dec_term_menu,
                                    &mut self.symbolic_variable_region.registry_mut(),
                                    attrs,
                                    variance,
                                ),
                                trai_syn_expr_idxs,
                            ),
                            CurrentTemplateVariableData::Constant {
                                ident_token,
                                ty_expr_idx,
                            } => {
                                let ty = self.infer_new_expr_term(ty_expr_idx).map_err(Into::into);
                                (
                                    ident_token.ident().into(),
                                    (
                                        ty,
                                        DecSymbolicVariable::new_const(
                                            self.db,
                                            self.toolchain,
                                            attrs,
                                            ty,
                                            &mut self.symbolic_variable_region.registry_mut(),
                                        ),
                                    ),
                                    &[],
                                )
                            }
                            _ => todo!(),
                        };
                    let trai_terms = trai_expr_idxs
                        .iter()
                        .map(|&trai_expr_idx| self.infer_new_expr_term(trai_expr_idx)) // it might panic, let's see
                        .collect();
                    self.symbolic_variable_region.add_new_template_variable(
                        self.db,
                        vars.start(),
                        ty,
                        term_symbol,
                        name,
                        trai_terms,
                    )
                }
                SyndicateTypeConstraint::SimpleParenateParameter {
                    syn_pattern_root,
                    ty,
                } => self.init_current_variable_signatures_in_parenate_or_lambda_parameter(
                    *syn_pattern_root,
                    *ty,
                    *vars,
                ),
                SyndicateTypeConstraint::SimpleClosureParameter { .. } => {
                    // p!(self.path());
                    todo!()
                }
                SyndicateTypeConstraint::FieldVariable {
                    ident_token,
                    ty_expr_idx,
                } => {
                    let ty = self.infer_new_expr_term(*ty_expr_idx).map_err(Into::into);
                    self.symbolic_variable_region
                        .add_new_field_variable_symbol_signature(
                            self.db,
                            vars.start(),
                            ty,
                            ident_token.ident().into(),
                        )
                }
                SyndicateTypeConstraint::LetPattern { .. }
                | SyndicateTypeConstraint::LoopVariable => {
                    // need only to compute for decl region
                    return;
                }
                SyndicateTypeConstraint::VariadicParenateParameter { ident_token, ty } => {
                    let ty = self.infer_new_expr_term(*ty).map_err(|_| todo!());
                    assert_eq!(vars.len(), 1);
                    let current_variable = vars.start();
                    let modifier = self.syn_expr_region_data[current_variable].modifier();
                    self.symbolic_variable_region.add_new_parenate_variable(
                        self.db,
                        current_variable,
                        modifier,
                        ty,
                        ident_token.ident().into(),
                    )
                }
            }
        }
    }

    /// explicit parameters are infered in this crate;
    ///
    /// let variables, be variables and match variables are infered in `husky-expr-ty`
    fn init_current_variable_signatures_in_parenate_or_lambda_parameter(
        &mut self,
        parenate_syn_pattern_root: ParenateParameterSynPatternRoot,
        ty: SynExprIdx,
        symbols: CurrentVariableIdxRange,
    ) {
        let Ok(ty) = self.infer_new_expr_term(ty) else {
            for symbol in symbols {
                let current_variable = &self.syn_expr_region_data[symbol];
                let name = current_variable.name();
                let modifier = current_variable.modifier();
                self.symbolic_variable_region.add_new_parenate_variable(
                    self.db,
                    symbol,
                    modifier,
                    Err(DecSymbolicVariableTypeErrorKind::CannotInferTypeExprTerm(
                        self.syn_expr_region_data.path(),
                    )),
                    name,
                )
            }
            return;
        };
        self.infer_pattern_tys_in_parenate_parameter(parenate_syn_pattern_root, ty);
        for symbol in symbols {
            self.infer_parenate_variable(symbol)
        }
    }

    fn infer_parenate_variable(&mut self, current_variable_idx: CurrentVariableIdx) {
        let current_variable = &self.syn_expr_region_data.variable_region()[current_variable_idx];
        match *current_variable.data() {
            CurrentVariableData::SimpleParenateParameter {
                ident,
                pattern_variable_idx,
            } => {
                let base_ty = self.pattern_variable_ty_infos[pattern_variable_idx].base_ty();
                self.symbolic_variable_region.add_new_parenate_variable(
                    self.db,
                    current_variable_idx,
                    current_variable.modifier(),
                    Ok(base_ty),
                    ident.into(),
                )
            }
            _ => unreachable!("this function is only used for explicit parameters"),
        }
    }

    fn infer_expr_roots(&mut self) {
        for expr_root in self.syn_expr_region_data.syn_expr_roots() {
            match expr_root.kind() {
                // omit props struct field because they are inferred for field variable
                SynExprRootKind::PropsStructFieldType { .. } => continue,
                SynExprRootKind::PrimalTrait
                | SynExprRootKind::ReturnType
                | SynExprRootKind::TupleStructFieldType
                | SynExprRootKind::ParenateParameterDefaultValue { .. }
                | SynExprRootKind::TypeAliasValue
                | SynExprRootKind::TypeVarDefault
                | SynExprRootKind::AssocTypeValue
                | SynExprRootKind::DefaultConstExclude
                | SynExprRootKind::Dep
                | SynExprRootKind::Proj => (),
                SynExprRootKind::SelfType => {
                    let self_ty_term = self.infer_new_expr_term(expr_root.syn_expr_idx()).ok();
                    self.symbolic_variable_region.set_self_ty(self_ty_term);
                    continue;
                }
                SynExprRootKind::RootBody
                | SynExprRootKind::LetStmtType
                | SynExprRootKind::LetStmtInitialValue
                | SynExprRootKind::HtmlArgumentExpr
                | SynExprRootKind::ReturnExpr
                | SynExprRootKind::Condition
                | SynExprRootKind::ConstantImplicitParameterType
                | SynExprRootKind::ExplicitParameterType
                | SynExprRootKind::FieldBindInitialValue { .. }
                | SynExprRootKind::Snippet
                | SynExprRootKind::ValExpr
                | SynExprRootKind::StaticExpr
                | SynExprRootKind::EvalExpr
                | SynExprRootKind::TraitInConstraint => continue,
                SynExprRootKind::Effect => todo!(),
            }
            self.cache_new_expr_term(expr_root.syn_expr_idx())
        }
    }

    // infer the term for expr, assuming it hasn't been computed before
    #[track_caller]
    fn infer_new_expr_term(
        &mut self,
        expr_idx: SynExprIdx,
    ) -> DerivedSynExprDecTermResult<DecTerm> {
        let result = self.calc_expr_term(expr_idx);
        let result_export = match result {
            Ok(term) => Ok(term),
            Err(_) => Err(DerivedSynExprDecTermError::DecTermAbortion),
        };
        self.save_expr_term(expr_idx, result);
        result_export
    }

    // cache the term for expr, assuming it hasn't been computed before
    #[track_caller]
    fn cache_new_expr_term(&mut self, expr_idx: SynExprIdx) {
        let result = self.calc_expr_term(expr_idx);
        self.save_expr_term(expr_idx, result)
    }

    pub(crate) fn finish(self) -> SynExprDecTermRegion {
        SynExprDecTermRegion::new(
            self.syn_expr_region_data.path(),
            self.symbolic_variable_region,
            self.expr_terms,
            self.pattern_ty_infos,
            self.pattern_variable_ty_infos,
        )
    }

    #[track_caller]
    fn save_expr_term(&mut self, expr_idx: SynExprIdx, outcome: SynExprDecTermResult<DecTerm>) {
        self.expr_terms.insert_new(expr_idx, outcome)
    }

    fn calc_expr_term(&mut self, expr_idx: SynExprIdx) -> SynExprDecTermResult<DecTerm> {
        let db = self.db;
        match self.syn_expr_region_data.expr_arena()[expr_idx] {
            SynExprData::Literal(token_idx, literal) => {
                Ok(DecTerm::from_literal_token_data(literal, db))
            }
            SynExprData::PrincipalEntityPath { opt_path, .. } => match opt_path {
                Some(path) => Ok(DecTerm::ItemPath(match path {
                    PrincipalEntityPath::Module(path) => {
                        husky_print_utils::p!(
                            self.syn_expr_region_data.path().debug(db),
                            path.debug(db)
                        );
                        todo!()
                    }
                    PrincipalEntityPath::MajorItem(path) => match path {
                        MajorItemPath::Type(path) => DecItemPath::Type(path),
                        MajorItemPath::Trait(path) => path.into(),
                        MajorItemPath::Form(path) => path.into(),
                    },
                    PrincipalEntityPath::TypeVariant(path) => DecItemPath::TypeVariant(path),
                })),
                None => Err(DerivedSynExprDecTermError::InvalidEntityPath.into()),
            },
            SynExprData::MajorItemPathAssocItem {
                parent_expr_idx,
                parent_path,
                colon_colon_regional_token,
                ident_token,
            } => todo!(),
            SynExprData::TypeAsTargetItem {
                ty,
                target: trai,
                ident,
                ..
            } => {
                let ty = self.infer_new_expr_term(ty)?;
                let trai = self.infer_new_expr_term(trai)?;
                Ok(DecTypeAsTraitItem::new(db, ty, trai, ident).into())
            }
            SynExprData::AssocItem {
                parent_expr_idx,
                colon_colon_regional_token_idx,
                ident,
                ident_regional_token_idx,
            } => {
                let parent = self.infer_new_expr_term(parent_expr_idx)?;
                match parent {
                    DecTerm::Literal(_) => todo!(),
                    DecTerm::SymbolicVariable(svar) => {
                        let symbolic_variable_obvious_trais = self
                            .symbolic_variable_region
                            .symbolic_variable_obvious_trais(svar)?;
                        match symbolic_variable_obvious_trais.len() {
                            0 => unreachable!(),
                            1 => {
                                let trai = symbolic_variable_obvious_trais[0];
                                Ok(DecTypeAsTraitItem::new(db, parent, trai, ident).into())
                            }
                            _ => todo!(),
                        }
                    }
                    DecTerm::AbstractVariable(_) => todo!(),
                    DecTerm::ItemPath(_) => todo!(),
                    DecTerm::Category(_) => todo!(),
                    DecTerm::Universe(_) => todo!(),
                    DecTerm::Curry(_) => todo!(),
                    DecTerm::Ritchie(_) => todo!(),
                    DecTerm::Abstraction(_) => todo!(),
                    DecTerm::Application(_) => todo!(),
                    DecTerm::ApplicationOrRitchieCall(_) => todo!(),
                    DecTerm::TypeAsTrait(parent) => {
                        Ok(
                            DecTypeAsTraitItem::new(db, parent.parent(db), parent.trai(db), ident)
                                .into(),
                        )
                    }
                    DecTerm::TypeAsTraitItem(_) => todo!(),
                    DecTerm::TraitConstraint(_) => todo!(),
                    DecTerm::LeashOrBitNot(_) => todo!(),
                    DecTerm::Wrapper(_) => todo!(),
                    DecTerm::List(_) => todo!(),
                }
            }
            SynExprData::InheritedVariable {
                inherited_variable_idx,
                ..
            } => self
                .symbolic_variable_region
                .inherited_variable_signature(inherited_variable_idx)
                .term()
                .map(Into::into)
                .ok_or(DerivedSynExprDecTermError::InheritedVariableIsNotValidTerm.into()),
            SynExprData::CurrentVariable {
                current_variable_idx,
                ..
            } => Ok(self
                .symbolic_variable_region
                .current_parameter_variable_signature(current_variable_idx)
                .expect("not none")
                .term()
                .ok_or(OriginalSynExprDecTermError::InvalidSymbolForTerm)?
                .into()),
            SynExprData::FrameVarDecl { .. } => unreachable!(),
            SynExprData::SelfType(_) => self
                .symbolic_variable_region
                .self_ty()
                .ok_or(DerivedSynExprDecTermError::SelfTypeNotAllowedInThisRegion.into()),
            SynExprData::SelfValue(_) => self
                .symbolic_variable_region
                .self_ty()
                .ok_or(DerivedSynExprDecTermError::SelfValueNotAllowedInThisRegion.into()),
            SynExprData::Binary {
                lopd, opr, ropd, ..
            } => {
                let Ok(lopd) = self.infer_new_expr_term(lopd) else {
                    return Err(
                        DerivedSynExprDecTermError::CannotInferOperandDecTermInPrefix.into(),
                    );
                };
                let Ok(ropd) = self.infer_new_expr_term(ropd) else {
                    return Err(
                        DerivedSynExprDecTermError::CannotInferOperandDecTermInPrefix.into(),
                    );
                };
                match opr {
                    SynBinaryOpr::Closed(_) => todo!(),
                    SynBinaryOpr::Shift(_) => todo!(),
                    SynBinaryOpr::Comparison(_) => todo!(),
                    SynBinaryOpr::ShortCircuitLogic(_) => todo!(),
                    SynBinaryOpr::AssignOrDefEq => todo!(),
                    SynBinaryOpr::AssignClosed(_) => todo!(),
                    SynBinaryOpr::AssignShift(_) => todo!(),
                    SynBinaryOpr::ScopeResolution => todo!(),
                    SynBinaryOpr::CurryType => Ok(DecCurry::new_nondependent(
                        self.db,
                        self.toolchain,
                        CurryKind::Explicit, // ad hoc
                        Variance::Invariant, // ad hoc
                        lopd,
                        ropd,
                    )
                    .into()),
                    SynBinaryOpr::As => todo!(),
                    // Ok(DecTypeAsTrait::new(db, lopd, ropd).into()),
                    SynBinaryOpr::Ins => todo!(),
                    SynBinaryOpr::In => todo!(),
                    SynBinaryOpr::Of => todo!(),
                }
            }
            SynExprData::Be { .. } => todo!(),
            SynExprData::Prefix { opr, opd, .. } => {
                let Ok(opd) = self.infer_new_expr_term(opd) else {
                    return Err(
                        DerivedSynExprDecTermError::CannotInferOperandDecTermInPrefix.into(),
                    );
                };
                let tmpl = match opr {
                    SynPrefixOpr::Minus => todo!(),
                    SynPrefixOpr::Not => todo!(),
                    SynPrefixOpr::Tilde => {
                        DecTerm::LeashOrBitNot(self.syn_expr_region_data.path().toolchain(self.db))
                    }
                    SynPrefixOpr::Ref => todo!(),
                    SynPrefixOpr::Option => self.dec_term_menu.option_ty_path(),
                };
                Ok(DecApplication::new(self.db, tmpl, opd).into())
            }
            SynExprData::Suffix { .. } => todo!(),
            SynExprData::Field { .. } => todo!(),
            SynExprData::MethodApplicationOrCall { .. } => todo!(),
            SynExprData::TemplateInstantiation {
                template,
                ref template_arguments,
            } => {
                let db = self.db;
                p!(
                    template_arguments.langle_regional_token_idx(),
                    self.syn_expr_region_data.path().debug(db),
                    template_arguments.rangle_regional_token_idx()
                );
                todo!();
                // let mut template_term = self.infer_new_expr_term(template)?;
                // for arg in template_arguments.arguments() {
                //     template_term = DecTermExplicitApplication::new(
                //         self.db,
                //         template_term,
                //         self.infer_new_expr_term(arg.syn_expr_idx())?,
                //     )
                //     .into()
                // }
                // Ok(template_term)
            }
            SynExprData::FunctionApplicationOrCall {
                function,
                ref template_arguments,
                ref items,
                ..
            } => {
                let Ok(function) = self.infer_new_expr_term(function) else {
                    return Err(
                        DerivedSynExprDecTermError::CannotInferArgumentDecTermInApplication.into(),
                    );
                };
                let template_arguments = match template_arguments {
                    Some(template_arguments) => template_arguments
                        .arguments()
                        .into_iter()
                        .map(|_| todo!())
                        .collect(),
                    None => vec![],
                };
                let extra_comma = match items.last() {
                    Some(last_item) => last_item.comma_regional_token_idx().is_some(),
                    None => false,
                };
                let items = items
                    .into_iter()
                    .map(|item| self.infer_new_expr_term(item.syn_expr_idx()))
                    .collect::<DerivedSynExprDecTermResult<_>>()?;
                Ok(DecApplicationOrRitchieCall::new(
                    function,
                    template_arguments,
                    items,
                    extra_comma,
                    self.db,
                )
                .into())
            }
            SynExprData::ExplicitApplication {
                function_expr_idx: function,
                argument_expr_idx: argument,
            } => {
                let Ok(argument) = self.infer_new_expr_term(argument) else {
                    Err(DerivedSynExprDecTermError::CannotInferArgumentDecTermInApplication)?
                };
                let Ok(function) = self.infer_new_expr_term(function) else {
                    Err(DerivedSynExprDecTermError::CannotInferFunctionDecTermInApplication)?
                };
                Ok(DecApplication::new(self.db, function, argument).into())
            }
            SynExprData::NewTuple { ref items, .. } => {
                p!(self.syn_expr_region_data.path().debug(self.db));
                p!(items.len());
                todo!()
            }
            SynExprData::List { ref items, .. } => {
                let items = items
                    .iter()
                    .map(|item| self.infer_new_expr_term(item.syn_expr_idx()))
                    .collect::<DerivedSynExprDecTermResult<Vec<_>>>()?;
                Ok(DecList::new(
                    self.db,
                    self.syn_expr_region_data.path().toolchain(self.db),
                    items,
                )
                .into())
            }
            SynExprData::BoxColonList { ref items, .. } => match items.len() {
                0 => Ok(self.dec_term_menu.slice_ty_path()),
                _ => todo!(),
            },
            SynExprData::Delimitered { item, .. } => {
                self.infer_new_expr_term(item).map_err(Into::into)
            }
            SynExprData::Block { stmts: _ } => todo!(),
            SynExprData::IndexOrCompositionWithList { .. } => todo!(),
            SynExprData::Err(ref e) => Err(DerivedSynExprDecTermError::ExprError.into()),
            SynExprData::At {
                at_regional_token_idx,
                place_label_regional_token,
            } => match place_label_regional_token {
                Some(_) => todo!(),
                None => match self.symbolic_variable_region.self_place() {
                    Some(place) => Ok(DecApplication::new(
                        self.db,
                        self.dec_term_menu.at_ty_path(),
                        place.into(),
                    )
                    .into()),
                    None => todo!(),
                },
            },
            SynExprData::Unit { .. } => Ok(self.dec_term_menu.unit()),
            SynExprData::EmptyHtmlTag {
                empty_html_bra_idx: langle_token_idx,
                function_ident,
                ref arguments,
                empty_html_ket,
            } => todo!(),
            SynExprData::FunctionCall { .. } => todo!(),
            SynExprData::Ritchie {
                ritchie_kind,
                ref parameter_ty_items,
                return_ty_syn_expr_idx: return_ty_expr,
                ..
            } => {
                let parameter_tys: SmallVec<[_; 2]> = parameter_ty_items
                    .into_iter()
                    .map(|parameter_ty_item| {
                        // todo: support variadic, and keyed??
                        Ok(DeclarativeRitchieSimpleParameter::new(
                            // todo: handle &mut !!
                            Contract::Pure,
                            self.infer_new_expr_term(parameter_ty_item.syn_expr_idx())?,
                        )
                        .into())
                    })
                    .collect::<SynExprDecTermResult<SmallVec<_>>>()?;
                let return_ty = match return_ty_expr {
                    Some(return_ty_expr) => self.infer_new_expr_term(return_ty_expr)?,
                    None => self.dec_term_menu.unit(),
                };
                Ok(DecRitchie::new(self.db, ritchie_kind, parameter_tys, return_ty).into())
            }
            SynExprData::Sorry { .. } => todo!(),
            SynExprData::Todo { .. } => todo!(),
            SynExprData::Unreachable { .. } => todo!(),
            SynExprData::NestedBlock { .. } => todo!(),
            SynExprData::Closure { .. } => todo!(),
        }
    }
}
