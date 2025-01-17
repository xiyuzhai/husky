use crate::*;
use lean_mir_expr::{
    expr::{LnMirExprData, LnMirExprEntry},
    tactic::{LnMirTacticData, LnMirTacticIdxRange},
};
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
        let ident = self.mangle_derivation(derivation);
        let ty = entry.prop().to_lean(self);
        let construction = match entry.construction() {
            VdMirDerivationConstruction::Ring(vd_mir_ring_derivation_construction) => todo!(),
            VdMirDerivationConstruction::Term(construction) => match *construction {
                VdMirTermDerivationConstruction::Literal => {
                    self.alloc_by_custom("term_derivation_literal", None)
                }
                VdMirTermDerivationConstruction::Variable => {
                    self.alloc_by_custom("term_derivation_variable", None)
                }
                VdMirTermDerivationConstruction::ItemPath => {
                    self.alloc_by_custom("term_derivation_item_path", None)
                }
                VdMirTermDerivationConstruction::Sum {
                    leader_equivalence,
                    ref follower_equivalences,
                } => self.alloc_by_custom("term_derivation_sum", None),
                VdMirTermDerivationConstruction::Sub { lopd, ropd } => {
                    self.alloc_by_custom("term_derivation_sub", None)
                }
                VdMirTermDerivationConstruction::Product {
                    leader_equivalence,
                    ref follower_equivalences,
                } => self.alloc_by_custom("term_derivation_product", None),
                VdMirTermDerivationConstruction::Div {
                    numerator,
                    denominator,
                } => self.alloc_by_custom("term_derivation_div", None),
                VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalence,
                    dst_term_equivalence,
                } => {
                    let arguments = [src_term_equivalence, dst_term_equivalence].to_lean(self);
                    self.alloc_by_custom("term_derivation_finalize", arguments)
                }
                VdMirTermDerivationConstruction::ChainingSeparatedList {
                    leader_equivalence,
                    ref follower_equivalences,
                } => self.alloc_by_custom("term_derivation_chaining_separated_list", None),
                VdMirTermDerivationConstruction::Square { radicand } => {
                    self.alloc_by_custom("term_derivation_square", None)
                }
                VdMirTermDerivationConstruction::Power { base, exponent } => {
                    self.alloc_by_custom("term_derivation_power", None)
                }
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
                } => LnMirTacticData::Assumption,
                _ => unreachable!(),
            },
        }
    }
}
