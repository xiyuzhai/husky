use lean_mir_expr::expr::LnMirExprEntry;
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

use super::*;

impl<'a> VdLeanTranspilationBuilder<'a, Dense> {
    pub(super) fn build_ln_tactic_from_vd_show(
        &mut self,
        prop: VdMirExprIdx,
        following_stmts: VdMirStmtIdxRange,
    ) -> LnMirTacticData {
        match *self.expr_arena()[prop].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: Some(joined_signature),
            } => self.build_show_nontrivial_chaining_separated_list(
                leader,
                followers,
                joined_signature,
            ),
            _ => {
                let ty = prop.to_lean(self);
                // It's intentional that this is transpiled to have tactic instead of show.
                // Lean's show will change the goal. However, until lean's show tactic can supply tactics for goal conversion, we will stick to have tactic.
                let construction_tactics: LnMirTacticIdxRange = following_stmts.to_lean(self);
                if construction_tactics.is_empty() {
                    use husky_print_utils::p;
                    p!(self.input(), following_stmts.len());
                    todo!()
                }
                let construction = self.alloc_expr(LnMirExprEntry::new(LnMirExprData::By {
                    tactics: construction_tactics,
                }));
                LnMirTacticData::Have {
                    ident: self.new_hypothesis_ident(),
                    ty: Some(ty),
                    construction,
                }
            }
        }
    }

    fn build_show_nontrivial_chaining_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseChainingSeparatorSignature, VdMirExprIdx)],
        joined_signature: VdBaseChainingSeparatorSignature,
    ) -> LnMirTacticData {
        todo!()
        // debug_assert!(followers.len() >= 2);
        // let ident = self.new_hypothesis_ident();
        // // TODO: Maye use to_lean trait method?
        // let tactic_data = LnMirTacticData::Calc {
        //     leader: leader.to_lean(self),
        //     followers: followers
        //         .iter()
        //         .copied()
        //         .map(|(func, expr)| {
        //             let LnMirFunc::BinaryOpr {
        //                 opr, instantiation, ..
        //             } = func.to_lean(self)
        //             else {
        //                 todo!()
        //             };
        //             ((opr, instantiation), expr.to_lean(self))
        //         })
        //         .collect(),
        // };
        // let ultimate_prop_function = VdMirFunc::NormalBaseSeparator(joined_signature).to_lean(self);
        // let ultimate_prop_arguments = [leader, followers.last().unwrap().1].to_lean(self);
        // let construction_data = LnMirExprData::By {
        //     tactics: self.alloc_tactics(vec![tactic_data]),
        // };
        // let construction = self.alloc_expr(construction_data);
        // tactics.push(LnMirTacticData::Have {
        //     ident,
        //     ty: self.alloc_expr(LnMirExprData::Application {
        //         function: ultimate_prop_function,
        //         arguments: ultimate_prop_arguments,
        //     }),
        //     construction,
        // });
    }
}
