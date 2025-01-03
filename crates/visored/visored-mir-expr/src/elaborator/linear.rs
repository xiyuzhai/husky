use hint::VdMirHintIdx;
use hypothesis::{construction::VdMirHypothesisConstruction, VdMirHypothesisIdx};

use super::*;
use crate::stmt::{VdMirStmtData, VdMirStmtMap};

#[derive(Default)]
pub struct VdMirSequentialElaborator<Inner>
where
    Inner: IsVdMirSequentialElaboratorInner,
{
    inner: Inner,
}

pub trait IsVdMirSequentialElaboratorInner {
    type HypothesisIdx: std::fmt::Debug + Eq;
    type Contradiction: std::fmt::Debug;

    fn elaborate_let_placeholder_stmt(&mut self) -> Result<(), Self::Contradiction>;

    fn elaborate_assume_stmt(
        &mut self,
        prop: VdMirExprIdx,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    fn elaborate_let_assigned_stmt(&mut self) -> Result<(), Self::Contradiction>;

    fn elaborate_goal_stmt(&mut self) -> Result<(), Self::Contradiction>;

    fn elaborate_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    fn elaborate_show_stmt(&mut self) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    fn elaborate_qed_stmt(&mut self) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    fn elaborate_expr(
        &mut self,
        expr: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    fn prune_explicit_hypothesis(
        &mut self,
        hypothesis: Self::HypothesisIdx,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) -> VdMirHypothesisIdx;
}

impl IsVdMirSequentialElaboratorInner for () {
    type HypothesisIdx = ();
    type Contradiction = ();

    fn elaborate_let_assigned_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_let_placeholder_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_assume_stmt(&mut self, prop: VdMirExprIdx) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_goal_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_show_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_qed_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_expr(
        &mut self,
        expr: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<(), ()> {
        Ok(())
    }

    fn prune_explicit_hypothesis(
        &mut self,
        hypothesis: (),
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) -> VdMirHypothesisIdx {
        hypothesis_constructor.construct_new_hypothesis(expr, VdMirHypothesisConstruction::Sorry)
    }
}

impl<Inner> VdMirSequentialElaborator<Inner>
where
    Inner: IsVdMirSequentialElaboratorInner,
{
    pub fn new(inner: Inner) -> Self {
        Self { inner }
    }
}

impl<Inner> IsVdMirTacticElaborator for VdMirSequentialElaborator<Inner>
where
    Inner: IsVdMirSequentialElaboratorInner,
{
    // # elaborate
    fn elaborate_stmts_ext(
        mut self,
        stmts: VdMirStmtIdxRange,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        self.elaborate_stmts(stmts, hypothesis_constructor);
    }

    fn elaborate_stmt_ext(
        mut self,
        stmt: VdMirStmtIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        self.elaborate_stmt(stmt, hypothesis_constructor);
    }

    fn elaborate_expr_ext(
        mut self,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        self.elaborate_expr(expr, hypothesis_constructor);
    }
}

impl<Inner> VdMirSequentialElaborator<Inner>
where
    Inner: IsVdMirSequentialElaboratorInner,
{
    fn elaborate_stmts(
        &mut self,
        stmts: VdMirStmtIdxRange,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        for stmt in stmts {
            self.elaborate_stmt(stmt, hypothesis_constructor);
        }
    }

    fn elaborate_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        match *hypothesis_constructor.stmt_arena()[stmt].data() {
            VdMirStmtData::Block { stmts, .. } => {
                self.elaborate_stmts(stmts, hypothesis_constructor)
            }
            VdMirStmtData::LetPlaceholder { .. } => {
                self.inner
                    .elaborate_let_placeholder_stmt()
                    .expect("handle contradiction");
            }
            VdMirStmtData::Assume { prop, .. } => {
                let hypothesis = self
                    .inner
                    .elaborate_assume_stmt(prop)
                    .expect("handle contradiction");
                let hypothesis =
                    self.inner
                        .prune_explicit_hypothesis(hypothesis, prop, hypothesis_constructor);
                hypothesis_constructor
                    .stmt_arena_mut()
                    .update(stmt, |entry| {
                        let VdMirStmtData::Assume {
                            hypothesis_place, ..
                        } = entry.data_mut()
                        else {
                            unreachable!()
                        };
                        hypothesis_place.set(Ok(hypothesis));
                    });
            }
            VdMirStmtData::LetAssigned { .. } => {
                let elaboration = self
                    .inner
                    .elaborate_let_assigned_stmt()
                    .expect("handle contradiction");
                todo!();
            }
            VdMirStmtData::Goal { .. } => {
                self.inner
                    .elaborate_goal_stmt()
                    .expect("handle contradiction");
            }
            VdMirStmtData::Have { prop, hint, .. } => {
                let hypothesis = self
                    .inner
                    .elaborate_have_stmt(stmt, prop, hint, hypothesis_constructor.region_data())
                    .expect("handle contradiction");
                let hypothesis =
                    self.inner
                        .prune_explicit_hypothesis(hypothesis, prop, hypothesis_constructor);
                hypothesis_constructor
                    .stmt_arena_mut()
                    .update(stmt, |entry| {
                        let VdMirStmtData::Have {
                            hypothesis_place, ..
                        } = entry.data_mut()
                        else {
                            unreachable!()
                        };
                        hypothesis_place.set(Ok(hypothesis));
                    });
            }
            VdMirStmtData::Show { .. } => {
                let elaboration = self
                    .inner
                    .elaborate_show_stmt()
                    .expect("handle contradiction");
                todo!();
            }
            VdMirStmtData::Qed {
                goal_and_hypothesis_place,
            } => {
                if let Some((goal, _)) = goal_and_hypothesis_place {
                    let hypothesis = self
                        .inner
                        .elaborate_qed_stmt()
                        .expect("handle contradiction");
                    let hypothesis = self.inner.prune_explicit_hypothesis(
                        hypothesis,
                        goal,
                        hypothesis_constructor,
                    );
                    hypothesis_constructor
                        .stmt_arena_mut()
                        .update(stmt, |entry| {
                            let VdMirStmtData::Qed {
                                goal_and_hypothesis_place: Some((_, hypothesis_place)),
                                ..
                            } = entry.data_mut()
                            else {
                                unreachable!()
                            };
                            hypothesis_place.set(Ok(hypothesis));
                        });
                }
            }
        }
    }

    fn elaborate_expr(
        &mut self,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor,
    ) {
        // ad hoc
        // todo!()
    }
}
