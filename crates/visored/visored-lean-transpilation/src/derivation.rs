pub mod litnum_bound;
pub mod term;

use crate::*;
use lean_mir_expr::{
    expr::{LnMirExprData, LnMirExprEntry},
    tactic::{LnMirTacticData, LnMirTacticIdxRange},
};
use visored_mir_expr::{
    coercion::VdMirCoercion,
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{
            term::{VdMirTermDerivationConstruction, VdMirTermDerivationIdx},
            VdMirDerivationConstruction,
        },
        VdMirDerivationIdx,
    },
    expr::VdMirExprIdx,
    hypothesis::{VdMirHypothesisEntry, VdMirHypothesisIdx},
};
use Argument::{Coercion as C, Derivation as D, Expr as E, Hypothesis as H};

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(crate) fn build_derivation_tactics(
        &mut self,
        derivation_chunk: VdMirDerivationChunk,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) -> LnMirTacticIdxRange {
        let mut derivations: Vec<LnMirTacticData> = vec![];
        for derivation in derivation_chunk.new_derivations() {
            derivations.push(self.build_derivation_tactic_data(derivation));
        }
        derivations
            .push(self.build_derivation_chunk_end_tactic_data(derivation_chunk.main_derivation()));
        self.alloc_tactics(derivations)
    }

    fn build_derivation_tactic_data(&mut self, derivation: VdMirDerivationIdx) -> LnMirTacticData {
        let entry = &self.derivation_arena()[derivation];
        let ident = self.mangle_derivation(derivation);
        let ty = entry.prop().to_lean(self);
        let construction = match entry.construction() {
            VdMirDerivationConstruction::Ring(construction) => todo!(),
            VdMirDerivationConstruction::Term(construction) => {
                self.build_term_tactic_construction(construction)
            }
            VdMirDerivationConstruction::LitnumBound(construction) => {
                self.build_litnum_bound_tactic_construction(construction)
            }
        };
        LnMirTacticData::Have {
            ident,
            ty: Some(ty),
            construction,
        }
    }

    fn build_derivation_chunk_end_tactic_data(
        &mut self,
        main_derivation: VdMirDerivationIdx,
    ) -> LnMirTacticData {
        match self.derivation_arena()[main_derivation].construction() {
            VdMirDerivationConstruction::Ring(construction) => match construction {
                _ => todo!(),
            },
            VdMirDerivationConstruction::Term(construction) => {
                self.build_term_derivation_chunk_end_tactic_data(construction)
            }
            VdMirDerivationConstruction::LitnumBound(construction) => {
                self.build_litnum_bound_derivation_chunk_end_tactic_data(construction)
            }
        }
    }
}

#[derive(Copy, Clone)]
enum Argument {
    Coercion(VdMirCoercion),
    Derivation(VdMirDerivationIdx),
    Expr(VdMirExprIdx),
    Hypothesis(VdMirHypothesisIdx),
}

impl<S> VdTranspileToLean<S, LnMirExprEntry> for Argument
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        match self {
            C(coercion) => coercion.to_lean(builder),
            D(derivation) => derivation.to_lean(builder),
            E(expr) => expr.to_lean(builder),
            H(hypothesis) => hypothesis.to_lean(builder),
        }
    }
}
