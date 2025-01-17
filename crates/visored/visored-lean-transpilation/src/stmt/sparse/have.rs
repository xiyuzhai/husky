use super::*;
use dictionary::func_key::VdFuncKeyTranslation;
use either::*;
use lean_mir_expr::{
    expr::{application::LnMirFunc, LnMirExprEntry},
    item_defn::def::LnMirDefBody,
    tactic::LnMirTacticData,
};
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::instantiation::LnInstantiation;
use visored_mir_expr::{
    expr::application::VdMirFunc,
    hint::VdMirHintIdxRange,
    hypothesis::{chunk::VdMirHypothesisChunk, VdMirHypothesisIdx},
};
use visored_mir_opr::{opr::binary::VdMirBaseBinaryOpr, separator::VdMirBaseSeparator};
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, VdBaseSeparatorSignature,
};

impl<'a> VdLeanTranspilationBuilder<'a, Sparse> {
    pub(super) fn build_have_stmt(
        &mut self,
        stmt: VdMirStmtIdx,
        prop: VdMirExprIdx,
        hypothesis_chunk: VdMirHypothesisChunk,
    ) -> LnItemDefnData {
        match *self.expr_arena()[prop].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: Some(joined_signature),
            } => self.build_then_nontrivial_chaining_separated_list(
                leader,
                followers,
                joined_signature,
            ),
            _ => {
                let ident = self.new_hypothesis_ident();
                let mut ln_tactics = vec![];
                self.build_have_tactics(stmt, hypothesis_chunk, &mut ln_tactics);
                let ln_tactics = self.alloc_tactics(ln_tactics);
                LnItemDefnData::Def {
                    ident,
                    parameters: vec![],
                    ty: Some(prop.to_lean(self)),
                    // TODO: better??
                    body: LnMirDefBody::Tactics(ln_tactics),
                }
            }
        }
    }

    fn build_then_nontrivial_chaining_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseChainingSeparatorSignature, VdMirExprIdx)],
        joined_signature: VdBaseChainingSeparatorSignature,
    ) -> LnItemDefnData {
        debug_assert!(followers.len() >= 2);
        let ident = self.new_hypothesis_ident();
        // TODO: Maye use to_lean trait method?
        let tactic_data = LnMirTacticData::Calc {
            leader: leader.to_lean(self),
            followers: followers
                .iter()
                .copied()
                .map(|(func, expr)| {
                    let LnMirFunc::BinaryOpr {
                        opr, instantiation, ..
                    } = func.to_lean(self)
                    else {
                        todo!()
                    };
                    ((opr, instantiation), expr.to_lean(self))
                })
                .collect(),
        };
        let ultimate_prop_function =
            VdMirFunc::NormalBaseSeparator(joined_signature.into()).to_lean(self);
        let ultimate_prop_arguments = [leader, followers.last().unwrap().1].to_lean(self);
        LnItemDefnData::Def {
            ident,
            parameters: vec![],
            ty: Some(self.alloc_expr(LnMirExprEntry::new(
                LnMirExprData::Application {
                    function: ultimate_prop_function,
                    arguments: ultimate_prop_arguments,
                },
                todo!(),
            ))),
            body: self.alloc_tactics([tactic_data]).into(),
        }
    }
}
