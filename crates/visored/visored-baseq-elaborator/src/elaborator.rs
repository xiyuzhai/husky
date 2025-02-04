use crate::{
    call::stack::VdBsqCallStack,
    expr::{VdBsqExpr, VdBsqExprData},
    hypothesis::{
        construction::VdBsqHypothesisConstruction,
        constructor::VdBsqHypothesisConstructor,
        contradiction::{VdBsqHypothesisContradiction, VdBsqHypothesisResult},
        VdBsqHypothesisIdx,
    },
    session::VdBsqSession,
    *,
};
use alt_maybe_result::*;
use alt_option::*;
use eterned::db::EternerDb;
use floated_sequential::db::FloaterDb;
use miracle::{error::MiracleAltMaybeResult, HasMiracle, Miracle};
use rustc_hash::FxHashMap;
use smallvec::*;
use std::marker::PhantomData;
use term::VdBsqTerm;
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_mir_expr::{
    elaborator::linear::{IsVdMirSequentialElaboratorInner, VdMirSequentialElaborator},
    expr::{
        application::VdMirFunc, VdMirExprArenaRef, VdMirExprIdx, VdMirExprIdxRange, VdMirExprMap,
        VdMirExprOrderedMap,
    },
    hint::VdMirHintIdx,
    hypothesis::{
        construction::VdMirHypothesisConstruction, constructor::VdMirHypothesisConstructor,
        VdMirHypothesisIdx,
    },
    pattern::VdMirPattern,
    region::VdMirExprRegionDataRef,
    stmt::{block::VdMirBlockKind, VdMirStmtData, VdMirStmtIdx},
};
use visored_mir_opr::{
    opr::binary::VdMirBaseBinaryOpr,
    separator::{folding::VdMirBaseFoldingSeparator, VdMirBaseSeparator},
};
use visored_signature::{
    menu::{vd_signature_menu, VdSignatureMenu},
    signature::separator::base::{
        chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
        VdBaseSeparatorSignature,
    },
};
use visored_term::{
    menu::{vd_ty_menu, VdTypeMenu},
    term::menu::{vd_term_menu, VdTermMenu},
};

pub struct VdBsqElaboratorInner<'db, 'sess> {
    session: &'sess VdBsqSession<'db>,
    term_menu: &'db VdTermMenu,
    ty_menu: &'db VdTypeMenu,
    signature_menu: &'db VdSignatureMenu,
    mir_to_bsq_expr_map: VdMirExprMap<VdBsqExpr<'sess>>,
    term_to_expr_map: FxHashMap<VdBsqTerm<'sess>, VdBsqExpr<'sess>>,
    miracle: Miracle,
    pub(crate) hc: VdBsqHypothesisConstructor<'db, 'sess>,
    pub(crate) call_stack: VdBsqCallStack,
}

impl<'db, 'sess> std::fmt::Debug for VdBsqElaboratorInner<'db, 'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VdBsqElaboratorInner").finish()
    }
}

pub type VdBsqElaborator<'db, 'sess> =
    VdMirSequentialElaborator<'db, VdBsqElaboratorInner<'db, 'sess>>;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn new(session: &'sess VdBsqSession<'db>, region_data: VdMirExprRegionDataRef) -> Self {
        Self {
            session,
            term_menu: vd_term_menu(session.eterner_db()),
            ty_menu: vd_ty_menu(session.eterner_db()),
            signature_menu: vd_signature_menu(session.eterner_db()),
            hc: VdBsqHypothesisConstructor::new(session),
            mir_to_bsq_expr_map: VdMirExprMap::new2(region_data.expr_arena),
            miracle: Miracle::new_uninitialized(),
            call_stack: VdBsqCallStack::new(),
            term_to_expr_map: FxHashMap::default(),
        }
    }
}

impl<'db, 'sess> HasMiracle for VdBsqElaboratorInner<'db, 'sess> {
    fn miracle(&self) -> &Miracle {
        &self.miracle
    }

    fn miracle_mut(&mut self) -> &mut Miracle {
        &mut self.miracle
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn session(&self) -> &'sess VdBsqSession<'db> {
        self.session
    }

    pub fn eterner_db(&self) -> &'db EternerDb {
        self.session.eterner_db()
    }

    pub fn floater_db(&self) -> &'sess FloaterDb {
        self.session.floater_db()
    }

    pub fn term_menu(&self) -> &'db VdTermMenu {
        self.term_menu
    }

    pub fn ty_menu(&self) -> &'db VdTypeMenu {
        self.ty_menu
    }

    pub fn signature_menu(&self) -> &'db VdSignatureMenu {
        self.signature_menu
    }

    pub fn call_stack(&self) -> &VdBsqCallStack {
        &self.call_stack
    }

    #[track_caller]
    pub fn expr_fld(&self, expr: VdMirExprIdx) -> VdBsqExpr<'sess> {
        self.mir_to_bsq_expr_map[expr]
    }

    pub(crate) fn mir_expr_to_bsq_map(&self) -> &VdMirExprMap<VdBsqExpr<'sess>> {
        &self.mir_to_bsq_expr_map
    }

    pub(crate) fn dispatch_table(&self) -> &'sess VdDefaultGlobalDispatchTable {
        self.session.dispatch_table()
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn save_expr_fld(&mut self, expr: VdMirExprIdx, fld: VdBsqExpr<'sess>) {
        self.mir_to_bsq_expr_map.insert_new(expr, fld);
    }

    pub(crate) fn do_term_to_expr(
        &mut self,
        term: impl Into<VdBsqTerm<'sess>>,
        f: impl FnOnce(&mut Self) -> VdBsqExpr<'sess>,
    ) -> VdBsqExpr<'sess> {
        let term = term.into();
        if let Some(&expr) = self.term_to_expr_map.get(&term) {
            expr
        } else {
            let expr = f(self);
            self.term_to_expr_map.insert(term, expr);
            expr
        }
    }
}

impl<'db, 'sess> IsVdMirSequentialElaboratorInner<'db> for VdBsqElaboratorInner<'db, 'sess> {
    type HypothesisIdx = VdBsqHypothesisIdx<'sess>;
    type Contradiction = VdBsqHypothesisContradiction<'sess>;

    fn enter_block(&mut self, kind: VdMirBlockKind) {
        match kind {
            VdMirBlockKind::Environment | VdMirBlockKind::Division => self.hc.enter_block(),
        }
    }

    fn exit_block(&mut self, kind: VdMirBlockKind) {
        match kind {
            VdMirBlockKind::Environment | VdMirBlockKind::Division => self.hc.exit_block(),
        }
    }

    fn elaborate_let_assigned_stmt(
        &mut self,
        pattern: &VdMirPattern,
        assignment: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        match *pattern {
            VdMirPattern::Letter {
                letter,
                symbol_local_defn,
            } => {
                let assignment = self.expr_fld(assignment);
                let variable = self.mk_expr(
                    VdBsqExprData::Variable(letter, symbol_local_defn),
                    assignment.ty(),
                );
                let signature = region_data.infer_eq_signature(assignment.ty(), assignment.ty());
                let eq_expr_data = VdBsqExprData::ChainingSeparatedList {
                    leader: variable,
                    followers: smallvec![(signature, assignment)],
                    joined_signature: None,
                };
                let prop = self.mk_expr(eq_expr_data, self.ty_menu().prop);
                Ok(self
                    .hc
                    .construct_new_hypothesis(prop, VdBsqHypothesisConstruction::LetAssigned))
            }
        }
    }

    fn elaborate_let_placeholder_stmt(&mut self) -> VdBsqHypothesisResult<'sess, ()> {
        Ok(())
    }

    fn elaborate_assume_stmt(
        &mut self,
        prop: VdMirExprIdx,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        Ok(self
            .hc
            .construct_new_hypothesis(self.expr_fld(prop), VdBsqHypothesisConstruction::Assume))
    }

    fn elaborate_goal_stmt(&mut self) -> VdBsqHypothesisResult<'sess, ()> {
        Ok(())
    }

    fn elaborate_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        region_data: VdMirExprRegionDataRef,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        let prop = self.mir_to_bsq_expr_map[prop];
        match hint {
            Some(hint) => todo!(),
            None => self.run_obvious(prop),
        }
    }

    fn elaborate_show_stmt(
        &mut self,
        goal: VdMirExprIdx,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        let goal = self.expr_fld(goal);
        self.run_obvious(goal)
    }

    fn elaborate_qed_stmt(
        &mut self,
        goal: VdMirExprIdx,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        let goal = self.expr_fld(goal);
        self.run_obvious(goal)
    }

    fn elaborate_field_div_expr(
        &mut self,
        divisor: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>> {
        let divisor = self.expr_fld(divisor);
        // TODO: use dispatch table
        let signature = if divisor.ty() == self.ty_menu().nat {
            self.signature_menu().nat_ne
        } else if divisor.ty() == self.ty_menu().int {
            self.signature_menu().int_ne
        } else if divisor.ty() == self.ty_menu().rat {
            self.signature_menu().rat_ne
        } else if divisor.ty() == self.ty_menu().real {
            self.signature_menu().real_ne
        } else {
            todo!("divisor.ty() = {:?}", divisor.ty())
        };
        let prop = self.mk_expr(
            VdBsqExprData::ChainingSeparatedList {
                leader: divisor,
                followers: smallvec![(signature, self.mk_zero())],
                joined_signature: None,
            },
            self.ty_menu().prop,
        );
        self.run_obvious(prop)
    }

    fn elaborate_folding_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseFoldingSeparatorSignature, VdMirExprIdx)],
    ) {
        let (fst_signature, fst) = followers[0];
        match fst_signature.separator() {
            VdMirBaseFoldingSeparator::CommRingAdd => (),
            VdMirBaseFoldingSeparator::CommRingMul => (),
            VdMirBaseFoldingSeparator::SetTimes => todo!(),
            VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
        }
    }

    fn elaborate_chaining_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseChainingSeparatorSignature, VdMirExprIdx)],
        joined_signature: Option<VdBaseChainingSeparatorSignature>,
    ) {
        // todo!()
    }

    fn cache_expr(&mut self, expr: VdMirExprIdx, region_data: VdMirExprRegionDataRef) {
        self.cache_mir_expr_to_bsq(expr, region_data);
    }

    fn transcribe_explicit_hypothesis(
        &mut self,
        hypothesis: Self::HypothesisIdx,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirHypothesisIdx {
        hypothesis.transcribe(self, Some(prop), hc)
    }

    fn transcribe_implicit_hypothesis(
        &mut self,
        hypothesis: VdBsqHypothesisIdx<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirHypothesisIdx {
        hypothesis.transcribe(self, None, hc)
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn run(&mut self, mut f: impl FnMut(&mut Self) -> Mhr<'sess>) -> Hr<'sess> {
        use miracle::HasMiracleFull;

        let stages = self.session().config().stages();
        assert!(stages.len() > 0, "stages must be non-empty");
        match self.run_stages(stages, f) {
            AltJustOk(res) => res,
            AltJustErr(_) | AltNothing => todo!(),
        }
    }

    pub fn run_obvious(&mut self, prop: VdBsqExpr<'sess>) -> Hr<'sess> {
        self.run(|slf| slf.obvious(prop))
    }
}
