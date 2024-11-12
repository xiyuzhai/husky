mod assign;
mod assign_closed;
mod assign_shift;
mod comparison;
mod pure_closed;
mod shift;

use husky_fly_term::{
    dispatch::instance::binary_opr::SemaBinaryOprInstanceDispatch,
    signature::assoc_item::trai_for_ty_item::binary_opr::SemaBinaryOprFlySignature,
};
use husky_sem_opr::binary::SemBinaryOpr;
use husky_syn_opr::SynBinaryOpr;
use sort_or_trai::ExpectSortOrTrait;

use super::*;

impl<'a> SemExprBuilder<'a> {
    /// .
    ///
    /// # Errors
    ///
    /// This function will return an error if .
    pub(super) fn calc_binary_expr_ty(
        &mut self,
        expr_idx: SynExprIdx,
        lopd: SynExprIdx,
        opr: SynBinaryOpr,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        let menu = self.term_menu();
        match opr {
            SynBinaryOpr::Closed(opr) => self.calc_binary_closed_expr_ty(lopd, ropd, opr, menu),
            SynBinaryOpr::Shift(opr) => self.calc_binary_shift_expr_ty(lopd, ropd, opr, menu),
            SynBinaryOpr::Comparison(opr) => self.calc_binary_comparison_expr_ty(lopd, opr, ropd),
            SynBinaryOpr::ShortCircuitLogic(opr) => {
                self.calc_binary_short_circuit_logic_expr_ty(lopd, opr, ropd)
            }
            SynBinaryOpr::AssignOrDefEq => self.calc_binary_assign_expr_ty(expr_idx, lopd, ropd),
            SynBinaryOpr::AssignClosed(opr) => {
                self.calc_binary_assign_closed_expr_ty(expr_idx, lopd, opr, ropd)
            }
            SynBinaryOpr::AssignShift(opr) => {
                self.calc_binary_assign_shift_expr_ty(expr_idx, lopd, opr, ropd)
            }
            SynBinaryOpr::ScopeResolution => {
                todo!()
                // Err(OriginalSemExprTypeError::TodoScopeResolution.into())
            }
            SynBinaryOpr::CurryType => self.calc_curry_expr_ty(lopd, ropd),
            SynBinaryOpr::As => self.calc_as_expr_ty(lopd, ropd),
            SynBinaryOpr::Ins => self.calc_ins_sem_expr(lopd, ropd),
            SynBinaryOpr::In => todo!(),
            SynBinaryOpr::Of => todo!(),
        }
    }

    fn calc_binary_short_circuit_logic_expr_ty(
        &mut self,
        lopd: SynExprIdx,
        opr: BinaryShortcuitLogicOpr,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        // todo: indirections
        let lopd_sem_expr_idx = self.build_expr(lopd, self.expect_argument_ty_bool());
        let ropd_sem_expr_idx = self.build_expr(ropd, self.expect_argument_ty_bool());
        (
            lopd_sem_expr_idx,
            SemBinaryOpr::ShortCircuitLogic(opr),
            ropd_sem_expr_idx,
            Ok(SemaBinaryOprInstanceDispatch::builtin()),
            Ok(self.term_menu().bool_ty_ontology().into()),
        )
    }

    fn calc_ins_sem_expr(
        &mut self,
        lopd: SynExprIdx,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        let (ropd_sem_expr_idx, ropd_ty) = self.build_expr_with_ty(ropd, ExpectAnyOriginal);
        let Some(ropd_ty) = ropd_ty else {
            let lopd_sem_expr_idx = self.build_expr(lopd, ExpectAnyDerived);
            return (
                lopd_sem_expr_idx,
                SemBinaryOpr::Ins,
                ropd_sem_expr_idx,
                todo!(),
                Err(DerivedSemExprTypeError::BinaryOperationRightOperandTypeNotInferred.into()),
            );
        };
        let lopd_sem_expr_idx = todo!();
        // todo
        // match ropd_ty {
        //     EthTerm::Entity(path) if path == self.item_path_menu.trai_ty().into() => {
        //         todo!()
        //     }
        //     EthTerm::Category(_) => {
        //         todo!()
        //         // if let Some(ropd_term) = self.infer_new_expr_term(ropd) {
        //         //     ropd_expectation = ExpectImplicitConversion {
        //         //         destination: ropd_term,
        //         //     }
        //         // }
        //     }
        //     _ => todo!(),
        // }
        (
            lopd_sem_expr_idx,
            SemBinaryOpr::Ins,
            ropd_sem_expr_idx,
            todo!(),
            Ok(self.term_menu().prop().into()),
        )
    }

    fn calc_as_expr_ty(
        &mut self,
        lopd: SynExprIdx,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        let (ropd_sem_expr_idx, ropd_ty) = self.build_expr_with_ty(ropd, ExpectSortOrTrait);
        let Some(ropd_ty) = ropd_ty else {
            use husky_print_utils::p;

            p!(
                self.syn_expr_region_data()[ropd].debug(self.db()),
                ropd_sem_expr_idx
                    .data_result(self.sem_expr_arena())
                    .debug(self.db()),
                ropd_sem_expr_idx
                    .ty_result(self.sem_expr_arena())
                    .debug(self.db())
            );
            todo!()
        };
        match ropd_ty.base_ty_data(self) {
            FlyBaseTypeData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ty_ethereal_term,
            } => todo!(),
            FlyBaseTypeData::Curry {
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyBaseTypeData::Hole(_, _) => todo!(),
            FlyBaseTypeData::Sort(_) => {
                let Some(ropd_term) = self.infer_expr_term(ropd_sem_expr_idx) else {
                    let lopd_sem_expr_idx = self.build_expr(lopd, ExpectAnyDerived);
                    return (
                        lopd_sem_expr_idx,
                        SemBinaryOpr::As,
                        ropd_sem_expr_idx,
                        todo!(),
                        Err(
                            DerivedSemExprTypeError::CastAsOperationRightOperandTermNotInferred
                                .into(),
                        ),
                    );
                };
                let lopd_sem_expr_idx = self.build_expr(lopd, ExpectCasting::new(ropd_term));
                (
                    lopd_sem_expr_idx,
                    SemBinaryOpr::As,
                    ropd_sem_expr_idx,
                    Ok(SemaBinaryOprInstanceDispatch::builtin()),
                    Ok(ropd_term),
                )
            }
            FlyBaseTypeData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyBaseTypeData::SymbolicVariable { symbolic_variable } => todo!(),
            FlyBaseTypeData::AbstractVariable { abstract_variable } => todo!(),
        }
    }

    fn calc_curry_expr_ty(
        &mut self,
        lopd: SynExprIdx,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        let expect_any_sort = ExpectSort::ANY;
        let (lopd_sem_expr_idx, lopd_universe) =
            self.build_expr_with_outcome(lopd, expect_any_sort);
        let Some(lopd_universe) = lopd_universe else {
            return (
                lopd_sem_expr_idx,
                SemBinaryOpr::CurryType,
                todo!(),
                todo!(),
                Err(DerivedSemExprTypeError::BinaryOperationLeftOperandTypeNotInferred.into()),
            );
        };
        let (ropd_sem_expr_idx, ropd_universe) =
            self.build_expr_with_outcome(ropd, expect_any_sort);
        let Some(ropd_universe) = ropd_universe else {
            return (
                lopd_sem_expr_idx,
                SemBinaryOpr::CurryType,
                ropd_sem_expr_idx,
                todo!(),
                Err(DerivedSemExprTypeError::BinaryOperationRightOperandTypeNotInferred.into()),
            );
        };
        todo!()
        // Ok(EthTerm::new_category(x_u.max(y_u)).into())
    }

    fn calc_binary_assign_shift_expr_ty(
        &mut self,
        expr_idx: SynExprIdx,
        lopd: SynExprIdx,
        opr: BinaryShiftOpr,
        ropd: SynExprIdx,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        todo!()
        // let expr_eval_lifetime = self
        //     .fly_term_region
        //     .new_implicit_symbol(expr_idx, ImplicitSymbolVariant::ExprEvalLifetime);
        // match self.infer_new_expr_ty_for_outcome(lopd, ExpectAnyOriginal) {
        //     Some(_) => todo!(),
        //     None => {
        //         self.infer_new_expr_ty_discarded(ropd, ExpectAnyDerived);
        //     }
        // };
        // Ok(self.term_menu().unit().into())
    }

    fn infer_basic_assign_ropd_ty(&mut self, lopd_ty: FlyTerm, ropd: SynExprIdx) {
        let (ropd_sem_expr_idx, ropd_ty) = self.build_expr_with_ty(ropd, ExpectAnyOriginal);
        let Some(ropd_ty) = ropd_ty else { return };
        todo!()
        // let lopd_ty = match lopd_ty {
        //     FlyTerm::EthTerm(lopd_ty) => match lopd_ty {
        //         EthTerm::Application(lopd_ty) => todo!(),
        //         _ => todo!(),
        //     },
        //     FlyTerm::Unresolved(lopd_ty) => {
        //         match self.fly_term_region[lopd_ty].unresolved_term() {
        //             FlyTermData::ImplicitSymbol(_) => todo!(),
        //             FlyTermData::TypeOntology(_) => {
        //                 todo!()
        //             }
        //             FlyTermData::Ritchie(_) => todo!(),
        //             FlyTermData::PlaceType { .. } => todo!(),
        //         }
        //     }
        //     _ => todo!(),
        // };
        // let ropd_ty = match ropd_ty {
        //     FlyTerm::EthTerm(ropd_ty) => todo!(),
        //     // self.db.intrinsic_ty(ropd_ty).reduced_term(),
        //     FlyTerm::Unresolved(_) => todo!(),
        //     _ => todo!(),
        // };
    }

    fn infer_composite_assign_ropd_ty(
        &mut self,
        lopd_ty: FlyTerm,
        opr: BinaryClosedOpr,
        ropd: SynExprIdx,
    ) {
        match opr {
            BinaryClosedOpr::Add => todo!(),
            BinaryClosedOpr::BitAnd => todo!(),
            BinaryClosedOpr::BitOr => todo!(),
            BinaryClosedOpr::BitXor => todo!(),
            BinaryClosedOpr::Div => todo!(),
            BinaryClosedOpr::Mul => todo!(),
            BinaryClosedOpr::RemEuclid => todo!(),
            BinaryClosedOpr::Power => todo!(),
            BinaryClosedOpr::Sub => todo!(),
        }
    }
}
