use std::marker::PhantomData;

use super::*;
use crate::stmt::{VdMirStmtData, VdMirStmtMap};
use expr::{application::VdMirFunc, VdMirExprData, VdMirExprIdxRange};
use hint::VdMirHintIdx;
use hypothesis::{
    chunk::VdMirHypothesisChunk, construction::VdMirHypothesisConstruction, VdMirHypothesisIdx,
};
use pattern::VdMirPattern;
use smallvec::SmallVec;
use smallvec::ToSmallVec;
use stmt::block::{VdMirBlockKind, VdMirBlockMeta};
use visored_mir_opr::{
    opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr},
    separator::VdMirBaseSeparator,
};
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;

#[derive(Default)]
pub struct VdMirSequentialElaborator<'db, Inner>
where
    Inner: IsVdMirSequentialElaboratorInner<'db>,
{
    inner: Inner,
    phantom: PhantomData<&'db ()>,
}

pub trait IsVdMirSequentialElaboratorInner<'db>: Sized {
    type HypothesisIdx: std::fmt::Debug + Eq;
    type Contradiction: std::fmt::Debug;

    fn enter_block(&mut self, kind: VdMirBlockKind);
    fn exit_block(&mut self, kind: VdMirBlockKind);

    /// # stmt
    fn elaborate_let_placeholder_stmt(&mut self) -> Result<(), Self::Contradiction>;
    fn elaborate_assume_stmt(
        &mut self,
        prop: VdMirExprIdx,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;
    fn elaborate_let_assigned_stmt(
        &mut self,
        pattern: &VdMirPattern,
        assignment: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;
    fn elaborate_goal_stmt(&mut self) -> Result<(), Self::Contradiction>;
    fn elaborate_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;
    fn elaborate_show_stmt(
        &mut self,
        goal: VdMirExprIdx,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;
    fn elaborate_qed_stmt(
        &mut self,
        goal: VdMirExprIdx,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;

    /// # expr
    fn elaborate_field_div_expr(
        &mut self,
        divisor: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction>;
    fn elaborate_folding_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
    );
    fn elaborate_chaining_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
        joined_signature: Option<VdBaseSeparatorSignature>,
    );
    fn cache_expr(&mut self, expr: VdMirExprIdx, region_data: VdMirExprRegionDataRef);

    fn transcribe_explicit_hypothesis(
        &self,
        hypothesis: Self::HypothesisIdx,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> VdMirHypothesisIdx;

    fn transcribe_implicit_hypothesis(
        &self,
        hypothesis: Self::HypothesisIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> VdMirHypothesisIdx;

    fn run<R>(
        db: &'db EternerDb,
        hypothesis_constructor: VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
        f: impl FnOnce(Self, VdMirHypothesisConstructor<'db, Self::HypothesisIdx>) -> R,
    ) -> R;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrivialHypothesisIdx {
    LetAssigned {
        assignment: VdMirExprIdx,
    },
    Assume {
        prop: VdMirExprIdx,
    },
    Have {
        prop: VdMirExprIdx,
    },
    Show {
        goal: VdMirExprIdx,
    },
    Qed {
        goal: VdMirExprIdx,
    },
    FieldDiv {
        divisor: idx_arena::ArenaIdx<expr::VdMirExprEntry>,
    },
}

impl<'db> IsVdMirSequentialElaboratorInner<'db> for () {
    type HypothesisIdx = TrivialHypothesisIdx;
    type Contradiction = ();

    fn enter_block(&mut self, kind: VdMirBlockKind) {}

    fn exit_block(&mut self, kind: VdMirBlockKind) {}

    fn elaborate_let_assigned_stmt(
        &mut self,
        pattern: &VdMirPattern,
        assignment: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) -> Result<TrivialHypothesisIdx, ()> {
        Ok(TrivialHypothesisIdx::LetAssigned { assignment })
    }

    fn elaborate_let_placeholder_stmt(&mut self) -> Result<(), ()> {
        Ok(())
    }

    fn elaborate_assume_stmt(&mut self, prop: VdMirExprIdx) -> Result<TrivialHypothesisIdx, ()> {
        Ok(TrivialHypothesisIdx::Assume { prop })
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
    ) -> Result<TrivialHypothesisIdx, ()> {
        Ok(TrivialHypothesisIdx::Have { prop })
    }

    fn elaborate_show_stmt(&mut self, goal: VdMirExprIdx) -> Result<TrivialHypothesisIdx, ()> {
        Ok(TrivialHypothesisIdx::Show { goal })
    }

    fn elaborate_qed_stmt(&mut self, goal: VdMirExprIdx) -> Result<TrivialHypothesisIdx, ()> {
        Ok(TrivialHypothesisIdx::Qed { goal })
    }

    fn elaborate_field_div_expr(
        &mut self,
        divisor: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> Result<Self::HypothesisIdx, Self::Contradiction> {
        Ok(TrivialHypothesisIdx::FieldDiv { divisor })
    }

    fn elaborate_folding_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
    ) {
        ()
    }

    fn elaborate_chaining_separated_list_expr(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
        joined_signature: Option<VdBaseSeparatorSignature>,
    ) {
        ()
    }

    fn cache_expr(&mut self, expr: VdMirExprIdx, region_data: VdMirExprRegionDataRef) {
        ()
    }

    fn transcribe_explicit_hypothesis(
        &self,
        hypothesis: TrivialHypothesisIdx,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> VdMirHypothesisIdx {
        hypothesis_constructor
            .construct_new_hypothesis(hypothesis, |_| (expr, VdMirHypothesisConstruction::Sorry))
    }

    fn transcribe_implicit_hypothesis(
        &self,
        hypothesis: TrivialHypothesisIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    ) -> VdMirHypothesisIdx {
        hypothesis_constructor.construct_new_hypothesis(hypothesis, |_| {
            (todo!(), VdMirHypothesisConstruction::Sorry)
        })
    }

    fn run<R>(
        db: &'db EternerDb,
        hypothesis_constructor: VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
        f: impl FnOnce(Self, VdMirHypothesisConstructor<'db, Self::HypothesisIdx>) -> R,
    ) -> R {
        f((), hypothesis_constructor)
    }
}

impl<'db, Inner> VdMirSequentialElaborator<'db, Inner>
where
    Inner: IsVdMirSequentialElaboratorInner<'db>,
{
    pub fn new(inner: Inner) -> Self {
        Self {
            inner,
            phantom: PhantomData,
        }
    }
}

impl<'db, Inner> IsVdMirTacticElaborator<'db> for VdMirSequentialElaborator<'db, Inner>
where
    Inner: IsVdMirSequentialElaboratorInner<'db>,
{
    type HypothesisIdx = Inner::HypothesisIdx;

    // # elaborate
    fn elaborate_stmts_ext(
        mut self,
        stmts: VdMirStmtIdxRange,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        self.elaborate_stmts(stmts, hypothesis_constructor);
    }

    fn elaborate_stmt_ext(
        mut self,
        stmt: VdMirStmtIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        self.elaborate_stmt(stmt, hypothesis_constructor);
    }

    fn elaborate_expr_ext(
        mut self,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        self.elaborate_expr(expr, hypothesis_constructor);
    }

    fn run<R>(
        db: &'db EternerDb,
        hypothesis_constructor: VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
        f: impl FnOnce(Self, VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>) -> R,
    ) -> R {
        Inner::run(
            db,
            hypothesis_constructor,
            |inner, hypothesis_constructor| f(Self::new(inner), hypothesis_constructor),
        )
    }
}

impl<'db, Inner> VdMirSequentialElaborator<'db, Inner>
where
    Inner: IsVdMirSequentialElaboratorInner<'db>,
{
    fn elaborate_stmts(
        &mut self,
        stmts: VdMirStmtIdxRange,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        for stmt in stmts {
            self.elaborate_stmt(stmt, hypothesis_constructor);
        }
    }

    fn elaborate_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        match *hypothesis_constructor.stmt_arena()[stmt].data() {
            VdMirStmtData::Block {
                stmts, ref meta, ..
            } => {
                let kind = meta.kind();
                self.inner.enter_block(kind);
                self.elaborate_stmts(stmts, hypothesis_constructor);
                self.inner.exit_block(kind);
            }
            VdMirStmtData::LetPlaceholder { .. } => {
                self.inner
                    .elaborate_let_placeholder_stmt()
                    .expect("handle contradiction");
            }
            VdMirStmtData::Assume { prop, .. } => {
                self.elaborate_expr(prop, hypothesis_constructor);
                let hypothesis = self
                    .inner
                    .elaborate_assume_stmt(prop)
                    .expect("handle contradiction");
                let hypothesis_chunk = self
                    .obtain_hypothesis_chunk_within_stmt_from_explicit_hypothesis(
                        stmt,
                        hypothesis,
                        prop,
                        hypothesis_constructor,
                    );
                hypothesis_constructor
                    .stmt_arena_mut()
                    .update(stmt, |entry| {
                        let VdMirStmtData::Assume {
                            hypothesis_chunk_place,
                            ..
                        } = entry.data_mut()
                        else {
                            unreachable!()
                        };
                        hypothesis_chunk_place.set(Ok(hypothesis_chunk));
                    });
            }
            VdMirStmtData::LetAssigned {
                ref pattern,
                assignment,
                ..
            } => {
                let pattern = pattern.clone();
                self.elaborate_expr(assignment, hypothesis_constructor);
                let hypothesis = self
                    .inner
                    .elaborate_let_assigned_stmt(
                        &pattern,
                        assignment,
                        hypothesis_constructor.region_data(),
                    )
                    .expect("handle contradiction");
                let hypothesis_chunk = self
                    .obtain_hypothesis_chunk_within_stmt_from_implicit_hypothesis(
                        stmt,
                        hypothesis,
                        hypothesis_constructor,
                    );
                hypothesis_constructor
                    .stmt_arena_mut()
                    .update(stmt, |entry| {
                        let VdMirStmtData::LetAssigned {
                            hypothesis_chunk_place,
                            ..
                        } = entry.data_mut()
                        else {
                            unreachable!()
                        };
                        hypothesis_chunk_place.set(Ok(hypothesis_chunk));
                    });
            }
            VdMirStmtData::Goal { .. } => {
                self.inner
                    .elaborate_goal_stmt()
                    .expect("handle contradiction");
            }
            VdMirStmtData::Have { prop, hint, .. } => {
                self.elaborate_expr(prop, hypothesis_constructor);
                let hypothesis = self
                    .inner
                    .elaborate_have_stmt(stmt, prop, hint, hypothesis_constructor.region_data())
                    .expect("handle contradiction");
                let hypothesis_chunk = self
                    .obtain_hypothesis_chunk_within_stmt_from_explicit_hypothesis(
                        stmt,
                        hypothesis,
                        prop,
                        hypothesis_constructor,
                    );
                hypothesis_constructor
                    .stmt_arena_mut()
                    .update(stmt, |entry| {
                        let VdMirStmtData::Have {
                            hypothesis_chunk_place,
                            ..
                        } = entry.data_mut()
                        else {
                            unreachable!()
                        };
                        hypothesis_chunk_place.set(Ok(hypothesis_chunk));
                    });
            }
            VdMirStmtData::Show {
                goal_and_hypothesis_chunk_place,
                ..
            } => {
                if let Some((goal, _)) = goal_and_hypothesis_chunk_place {
                    self.elaborate_expr(goal, hypothesis_constructor);
                    let hypothesis = self
                        .inner
                        .elaborate_show_stmt(goal)
                        .expect("handle contradiction");
                    let hypothesis_chunk = hypothesis_constructor
                        .obtain_hypothesis_chunk_within_stmt(stmt, |hypothesis_constructor| {
                            self.inner.transcribe_explicit_hypothesis(
                                hypothesis,
                                goal,
                                hypothesis_constructor,
                            )
                        });
                    hypothesis_constructor
                        .stmt_arena_mut()
                        .update(stmt, |entry| {
                            let VdMirStmtData::Show {
                                goal_and_hypothesis_chunk_place: Some((_, hypothesis_chunk_place)),
                                ..
                            } = entry.data_mut()
                            else {
                                unreachable!()
                            };
                            hypothesis_chunk_place.set(Ok(hypothesis_chunk));
                        });
                }
            }
            VdMirStmtData::Qed {
                goal_and_hypothesis_chunk_place,
            } => {
                if let Some((goal, _)) = goal_and_hypothesis_chunk_place {
                    self.elaborate_expr(goal, hypothesis_constructor);
                    let hypothesis = self
                        .inner
                        .elaborate_qed_stmt(goal)
                        .expect("handle contradiction");
                    let hypothesis_chunk = hypothesis_constructor
                        .obtain_hypothesis_chunk_within_stmt(stmt, |hypothesis_constructor| {
                            self.inner.transcribe_explicit_hypothesis(
                                hypothesis,
                                goal,
                                hypothesis_constructor,
                            )
                        });
                    hypothesis_constructor
                        .stmt_arena_mut()
                        .update(stmt, |entry| {
                            let VdMirStmtData::Qed {
                                goal_and_hypothesis_chunk_place: Some((_, hypothesis_chunk_place)),
                                ..
                            } = entry.data_mut()
                            else {
                                unreachable!()
                            };
                            hypothesis_chunk_place.set(Ok(hypothesis_chunk));
                        });
                }
            }
        }
    }

    fn obtain_hypothesis_chunk_within_stmt_from_explicit_hypothesis(
        &mut self,
        stmt: VdMirStmtIdx,
        hypothesis: Inner::HypothesisIdx,
        prop: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) -> VdMirHypothesisChunk {
        hypothesis_constructor.obtain_hypothesis_chunk_within_stmt(stmt, |hypothesis_constructor| {
            self.inner
                .transcribe_explicit_hypothesis(hypothesis, prop, hypothesis_constructor)
        })
    }

    fn obtain_hypothesis_chunk_within_stmt_from_implicit_hypothesis(
        &self,
        stmt: VdMirStmtIdx,
        hypothesis: Inner::HypothesisIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) -> VdMirHypothesisChunk {
        hypothesis_constructor.obtain_hypothesis_chunk_within_stmt(stmt, |hypothesis_constructor| {
            self.inner
                .transcribe_implicit_hypothesis(hypothesis, hypothesis_constructor)
        })
    }

    fn elaborate_expr(
        &mut self,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        // ad hoc
        // TODO: store expr elaboration in expr arena
        match *hypothesis_constructor.expr_arena()[expr].data() {
            VdMirExprData::Literal(_) | VdMirExprData::Variable(_) => (),
            VdMirExprData::Application {
                function,
                arguments,
            } => {
                if let Some(function) = function.expr() {
                    self.elaborate_expr(function, hypothesis_constructor);
                }
                for arg in arguments {
                    self.elaborate_expr(arg, hypothesis_constructor);
                }
                self.elaborate_application_expr(expr, function, arguments, hypothesis_constructor);
            }
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                // need to do this to avoid rustc complaining
                // we could also unsafe this
                let followers: SmallVec<[(VdMirFunc, VdMirExprIdx); 4]> = followers.to_smallvec();
                let followers: &[(VdMirFunc, VdMirExprIdx)] = &followers;
                self.elaborate_expr(leader, hypothesis_constructor);
                for &(_, follower) in followers {
                    self.elaborate_expr(follower, hypothesis_constructor);
                }
                self.inner
                    .elaborate_folding_separated_list_expr(leader, followers)
            }
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => {
                // need to do this to avoid rustc complaining
                // we could also unsafe this
                let followers: SmallVec<[(VdMirFunc, VdMirExprIdx); 4]> = followers.to_smallvec();
                let followers: &[(VdMirFunc, VdMirExprIdx)] = &followers;
                self.elaborate_expr(leader, hypothesis_constructor);
                for &(_, follower) in followers {
                    self.elaborate_expr(follower, hypothesis_constructor);
                }
                self.inner.elaborate_chaining_separated_list_expr(
                    leader,
                    followers,
                    joined_signature,
                )
            }
            VdMirExprData::ItemPath(vd_item_path) => (),
        }
        self.inner
            .cache_expr(expr, hypothesis_constructor.region_data());
    }

    fn elaborate_application_expr(
        &mut self,
        expr: VdMirExprIdx,
        function: VdMirFunc,
        arguments: VdMirExprIdxRange,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Inner::HypothesisIdx>,
    ) {
        match function {
            VdMirFunc::NormalBasePrefixOpr(signature) => match signature.opr {
                VdMirBasePrefixOpr::RingPos => (),
                VdMirBasePrefixOpr::RingNeg => (),
                _ => todo!(),
            },
            VdMirFunc::NormalBaseSeparator(signature) => todo!(),
            VdMirFunc::NormalBaseBinaryOpr(signature) => match signature.opr {
                VdMirBaseBinaryOpr::CommRingSub => (),
                VdMirBaseBinaryOpr::CommFieldDiv => {
                    let _ = self.inner.elaborate_field_div_expr(
                        arguments.last().unwrap(),
                        hypothesis_constructor,
                    );
                    // ad hoc, should save this somewhere
                    // todo!()
                }
            },
            // ad hoc, should check very carefully that one of the following holds:
            // - the base is positive
            // - the base is zero and the exponent is positive
            // - the exponent is a positive integer
            // - the base is nonzero and the exponent is zero
            VdMirFunc::Power(signature) => (),
            VdMirFunc::InSet => todo!(),
            VdMirFunc::NormalBaseSqrt(signature) => (), // ad hoc, should be merged with power
        }
    }
}
