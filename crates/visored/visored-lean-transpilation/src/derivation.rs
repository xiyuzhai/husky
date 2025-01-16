use crate::*;
use lean_mir_expr::tactic::{LnMirTacticData, LnMirTacticIdxRange};
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{term::VdMirTermDerivationConstruction, VdMirDerivationConstruction},
        VdMirDerivationIdx,
    },
    hypothesis::VdMirHypothesisEntry,
};

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
        let ident = self.mangle_derivation();
        let ty = entry.prop().to_lean(self);
        let construction = match entry.construction() {
            VdMirDerivationConstruction::Ring(vd_mir_ring_derivation_construction) => todo!(),
            VdMirDerivationConstruction::Term(construction) => match construction {
                VdMirTermDerivationConstruction::Literal => todo!(),
                VdMirTermDerivationConstruction::Variable => todo!(),
                VdMirTermDerivationConstruction::ItemPath => todo!(),
                VdMirTermDerivationConstruction::Sum {
                    summand_term_equivalences,
                } => todo!(),
                VdMirTermDerivationConstruction::Sub { lopd, ropd } => todo!(),
                VdMirTermDerivationConstruction::Product {
                    leader_equivalence,
                    follower_equivalences,
                } => todo!(),
                VdMirTermDerivationConstruction::Div {
                    numerator,
                    denominator,
                } => todo!(),
                VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalence,
                    dst_term_equivalence,
                } => todo!(),
                VdMirTermDerivationConstruction::ChainingSeparatedList {
                    leader_equivalence,
                    follower_equivalences,
                } => todo!(),
            },
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
            VdMirDerivationConstruction::Term(construction) => match construction {
                VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalence,
                    dst_term_equivalence,
                } => todo!(),
                _ => unreachable!(),
            },
        }
        LnMirTacticData::Apply {
            hypothesis: todo!(),
        }
    }
}
