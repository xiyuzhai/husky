use std::marker::PhantomData;
use visored_mir_expr::{
    elaborator::linear::{IsVdMirSequentialElaboratorInner, VdMirSequentialElaborator},
    expr::{VdMirExprArenaRef, VdMirExprIdx, VdMirExprMap, VdMirExprOrderedMap},
    hint::VdMirHintIdx,
    hypothesis::{
        construction::VdMirHypothesisConstruction, constructor::VdMirHypothesisConstructor,
        VdMirHypothesisIdx,
    },
    region::VdMirExprRegionDataRef,
    stmt::{VdMirStmtData, VdMirStmtIdx},
};

use crate::{
    expr::{build_expr_to_fld_map, VdMirExprFld},
    hypothesis::{
        construction::VdBaseqHypothesisConstruction,
        constructor::VdBaseqHypothesisConstructor,
        contradiction::{VdBaseqHypothesisContradiction, VdBaseqHypothesisResult},
        VdBaseqHypothesisIdx,
    },
    session::VdBaseqSession,
};

pub struct VdBaseqElaboratorInner<'db, 'sess> {
    session: &'sess VdBaseqSession<'db>,
    expr_to_fld_map: VdMirExprOrderedMap<VdMirExprFld<'sess>>,
    pub(crate) hypothesis_constructor: VdBaseqHypothesisConstructor<'db, 'sess>,
}

pub type VdBaseqElaborator<'db, 'sess> =
    VdMirSequentialElaborator<VdBaseqElaboratorInner<'db, 'sess>>;

impl<'db, 'sess> VdBaseqElaboratorInner<'db, 'sess> {
    pub fn new(session: &'sess VdBaseqSession<'db>, region_data: VdMirExprRegionDataRef) -> Self {
        Self {
            session,
            hypothesis_constructor: VdBaseqHypothesisConstructor::new(session),
            expr_to_fld_map: build_expr_to_fld_map(session, region_data),
        }
    }
}

impl<'db, 'sess> VdBaseqElaboratorInner<'db, 'sess> {
    pub fn session(&self) -> &'sess VdBaseqSession<'db> {
        self.session
    }
}

impl<'db, 'sess> IsVdMirSequentialElaboratorInner for VdBaseqElaboratorInner<'db, 'sess> {
    type HypothesisIdx = VdBaseqHypothesisIdx<'sess>;
    type Contradiction = VdBaseqHypothesisContradiction<'sess>;

    fn elaborate_let_assigned_stmt(&mut self) -> VdBaseqHypothesisResult<'sess, ()> {
        Ok(())
    }

    fn elaborate_let_placeholder_stmt(&mut self) -> VdBaseqHypothesisResult<'sess, ()> {
        Ok(())
    }

    fn elaborate_assume_stmt(
        &mut self,
        prop: VdMirExprIdx,
    ) -> VdBaseqHypothesisResult<'sess, VdBaseqHypothesisIdx<'sess>> {
        todo!()
        // Ok(())
    }

    fn elaborate_goal_stmt(&mut self) -> VdBaseqHypothesisResult<'sess, ()> {
        Ok(())
    }

    fn elaborate_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        region_data: VdMirExprRegionDataRef,
    ) -> VdBaseqHypothesisResult<'sess, VdBaseqHypothesisIdx<'sess>> {
        let prop = self.expr_to_fld_map[prop];
        match hint {
            Some(hint) => todo!(),
            None => self.obvious(prop),
        }
    }

    fn elaborate_show_stmt(
        &mut self,
    ) -> VdBaseqHypothesisResult<'sess, VdBaseqHypothesisIdx<'sess>> {
        todo!()
    }

    fn elaborate_qed_stmt(
        &mut self,
    ) -> VdBaseqHypothesisResult<'sess, VdBaseqHypothesisIdx<'sess>> {
        todo!()
    }

    fn elaborate_expr(
        &mut self,
        expr: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction> {
        todo!()
    }

    fn prune_explicit_hypothesis(
        &mut self,
        hypothesis: Self::HypothesisIdx,
        goal: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) -> VdMirHypothesisIdx {
        let construction = match *self.hypothesis_constructor.arena()[hypothesis].construction() {
            VdBaseqHypothesisConstruction::Sorry => VdMirHypothesisConstruction::Sorry,
            VdBaseqHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion: self.prune_coercion(is_real_coercion, hypothesis_constructor),
            },
            VdBaseqHypothesisConstruction::Phantom(phantom_data) => todo!(),
        };
        hypothesis_constructor.construct_new_hypothesis(goal, construction)
    }
}
