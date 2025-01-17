use lean_entity_path::LnItemPath;
use lean_mir_expr::{
    item_defn::def::{LnDefParameter, LnMirDefBody},
    tactic::LnMirTacticData,
};
use lean_term::ty::LnType;
use visored_entity_path::{environment::VdEnvironmentPath, module::VdModulePath};

use super::*;

impl<'a> VdLeanTranspilationBuilder<'a, Dense> {
    pub(crate) fn transpile_vd_stmts_to_ln_defns(
        &mut self,
        stmts: VdMirStmtIdxRange,
    ) -> LnItemDefnIdxRange {
        if stmts.is_empty() {
            return self.alloc_item_defns(vec![], vec![]);
        }
        match *self.stmt_arena()[stmts.first().unwrap()].data() {
            VdMirStmtData::Block { .. } => self.build_ln_item_defns_from_vd_blocks(stmts),
            _ => {
                let defn = self.build_ln_item_defn_from_vd_stmts(stmts);
                self.alloc_item_defns([defn], [LnItemDefnComment::Void])
            }
        }
    }
}

impl<'a> VdLeanTranspilationBuilder<'a, Dense> {
    fn build_ln_item_defns_from_vd_blocks(
        &mut self,
        stmts: VdMirStmtIdxRange,
    ) -> LnItemDefnIdxRange {
        let item_defns: Vec<_> = stmts
            .into_iter()
            .map(|stmt| self.build_ln_item_defn_from_vd_block(stmt))
            .collect();
        let source_map = self.source_map();
        let input = self.input();
        let token_storage = self.token_storage();
        let sem_sentence_range_map = self.sem_sentence_range_map();
        self.alloc_item_defns(
            item_defns,
            stmts.into_iter().map(|stmt| {
                let token_idx_range = match source_map[stmt] {
                    VdMirStmtSource::Block(_)
                    | VdMirStmtSource::Division(_)
                    | VdMirStmtSource::Clause(_) => return LnItemDefnComment::Void,
                    VdMirStmtSource::Qed => return LnItemDefnComment::Qed,
                    VdMirStmtSource::Sentence(sentence) => sem_sentence_range_map[sentence],
                };
                let offset_range = token_storage.token_idx_range_offset_range(token_idx_range);
                LnItemDefnComment::from_latex_source(&input[offset_range])
            }),
        )
    }

    fn build_ln_item_defn_from_vd_block(&mut self, stmt: VdMirStmtIdx) -> LnItemDefnData {
        let db = self.db();
        match *self.stmt_arena()[stmt].data() {
            VdMirStmtData::Block { stmts, ref meta } => {
                match *meta {
                    VdMirBlockMeta::Environment(_, environment_path, module_path) => {
                        let defn = self.with_module_path(module_path, |builder| {
                            builder.build_ln_item_defn_from_vd_stmts(stmts)
                        });
                        let defn = self.alloc_item_defn(defn, LnItemDefnComment::Void);
                        LnItemDefnData::Group {
                            defns: LnItemDefnIdxRange::new_single(defn),
                            meta: LnMirItemDefnGroupMeta::Environment(
                                vd_module_path_to_ln_namespace(module_path, db).unwrap(), // TODO: maybe not unwrap here?
                            ),
                        }
                    }
                    VdMirBlockMeta::Division(_, module_path) => {
                        let defns =
                            self.with_module_path(module_path, |builder| stmts.to_lean(builder));
                        LnItemDefnData::Group {
                            defns,
                            meta: LnMirItemDefnGroupMeta::Division(vd_module_path_to_ln_namespace(
                                module_path,
                                db,
                            )),
                        }
                    }
                }
            }
            VdMirStmtData::LetPlaceholder { .. }
            | VdMirStmtData::Assume { .. }
            | VdMirStmtData::LetAssigned { .. }
            | VdMirStmtData::Have { .. }
            | VdMirStmtData::Show { .. }
            | VdMirStmtData::Goal { .. }
            | VdMirStmtData::Qed { .. } => unreachable!(),
        }
    }

    fn build_ln_item_defn_from_vd_stmts(&mut self, stmts: VdMirStmtIdxRange) -> LnItemDefnData {
        let ident = self.mangle_stmts_item_defn();
        let mut parameters: Vec<LnDefParameter> = vec![];
        let mut goal = None;
        for stmt in stmts {
            match self.build_ln_parameter_from_vd_stmt(stmt, &mut parameters) {
                std::ops::ControlFlow::Continue(()) => (),
                std::ops::ControlFlow::Break(goal1) => {
                    goal = goal1;
                    break;
                }
            }
        }
        LnItemDefnData::Def {
            ident,
            parameters,
            ty: goal.map(|goal| goal.to_lean(self)),
            body: LnMirDefBody::Tactics(stmts.to_lean(self)),
        }
    }

    fn build_ln_def_from_vd_environment(
        &mut self,
        stmts: VdMirStmtIdxRange,
        environment_path: VdEnvironmentPath,
        module_path: VdModulePath,
    ) -> LnItemDefnData {
        // ad hoc
        let ident = self.mangle_stmts_item_defn();
        let mut parameters: Vec<LnDefParameter> = vec![];
        let mut goal: Option<VdMirExprIdx> = None;
        for stmt in stmts {
            match self.build_ln_parameter_from_vd_stmt(stmt, &mut parameters) {
                std::ops::ControlFlow::Continue(()) => (),
                std::ops::ControlFlow::Break(goal1) => {
                    goal = goal;
                    break;
                }
            }
        }
        LnItemDefnData::Def {
            ident,
            parameters,
            ty: goal.map(|goal| goal.to_lean(self)),
            body: LnMirDefBody::Tactics(stmts.to_lean(self)),
        }
    }

    fn build_ln_parameter_from_vd_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        parameters: &mut Vec<LnDefParameter>,
    ) -> std::ops::ControlFlow<Option<VdMirExprIdx>> {
        let stmt_arena = self.stmt_arena();
        match *stmt_arena[stmt].data() {
            VdMirStmtData::LetPlaceholder { ref pattern, ty } => {
                parameters.push(LnDefParameter {
                    ident: match *pattern {
                        VdMirPattern::Letter {
                            letter,
                            symbol_local_defn,
                        } => self.mangle_symbol(symbol_local_defn),
                    },
                    ty: ty.to_lean(self),
                });
                std::ops::ControlFlow::Continue(())
            }
            VdMirStmtData::Assume { prop, .. } => {
                parameters.push(LnDefParameter {
                    ident: self.mangle_assume(),
                    ty: prop.to_lean(self),
                });
                std::ops::ControlFlow::Continue(())
            }
            VdMirStmtData::Block { stmts, ref meta } => {
                for stmt in stmts {
                    match self.build_ln_parameter_from_vd_stmt(stmt, parameters) {
                        std::ops::ControlFlow::Continue(()) => (),
                        std::ops::ControlFlow::Break(b) => return std::ops::ControlFlow::Break(b),
                    }
                }
                std::ops::ControlFlow::Continue(())
            }
            VdMirStmtData::Goal { prop } => std::ops::ControlFlow::Break(Some(prop)),
            _ => std::ops::ControlFlow::Break(None),
        }
    }
}

/// the rust documentation doesn't explain very clearly how `map_while` works
#[test]
fn map_while_documentation_works() {
    #[track_caller]
    fn t(a: &[bool], expected: usize) {
        let len = a.iter().copied().map_while(|a| a.then_some(())).count();
        assert_eq!(expected, len);
    }
    t(&[true, false, true], 1);
    t(&[true, true, true], 3);
}
