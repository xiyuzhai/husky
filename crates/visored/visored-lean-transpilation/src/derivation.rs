use crate::*;
use lean_mir_expr::{
    expr::{LnMirExprData, LnMirExprEntry},
    tactic::{LnMirTacticData, LnMirTacticIdxRange},
};
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk, construction::VdMirDerivationConstruction, VdMirDerivationIdx,
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
        let ident = self.mangle_derivation(derivation);
        let ty = entry.prop().to_lean(self);
        let construction = match entry.construction() {
            VdMirDerivationConstruction::Ring(construction) => todo!(),
            VdMirDerivationConstruction::Term(construction) => todo!(),
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
                _ => todo!(),
            },
        }
    }
}
