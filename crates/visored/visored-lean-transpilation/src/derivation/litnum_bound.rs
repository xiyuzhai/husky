use super::*;
use convert_case::{Case, Casing};
use either::*;
use lean_entity_path::{
    theorem::{LnTermDerivationTheoremPath, LnTheoremPath},
    LnItemPath,
};
use lean_mir_expr::expr::{application::LnMirFunc, LnMirExprIdx, LnMirExprIdxRange};
use smallvec::*;
use visored_mir_expr::{
    coercion::{VdMirCoercion, VdMirSeparatorCoercion},
    derivation::construction::{
        litnum_bound::VdMirLitnumBoundDerivationConstruction,
        term::{VdMirTermDerivationConstruction, VdMirTermDerivationIdx},
    },
    expr::{VdMirExprEntry, VdMirExprIdx},
    hypothesis::VdMirHypothesisIdx,
};
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_litnum_bound_tactic_construction(
        &mut self,
        construction: &VdMirLitnumBoundDerivationConstruction,
    ) -> LnMirExprIdx {
        let variant_name: &'static str = construction.into();
        let arguments: Option<LnMirExprIdxRange> = match *construction {
            VdMirLitnumBoundDerivationConstruction::Normalize { separator } => {
                Some([A(separator.unicode())].to_lean(self))
            }
            VdMirLitnumBoundDerivationConstruction::Finish {
                a_opr,
                b_opr,
                src,
                src_nf_dn,
                dst_nf_dn,
                src_nf_and_dst_nf_equivalence_dn,
                src_sub_coercion,
                dst_sub_coercion,
                src_cmp_coercion,
                dst_cmp_coercion,
            } => Some(
                [
                    A(a_opr.unicode()),
                    A(b_opr.unicode()),
                    H(src),
                    D(*src_nf_dn),
                    D(*dst_nf_dn),
                    D(*src_nf_and_dst_nf_equivalence_dn),
                    C(src_sub_coercion.into()),
                    C(dst_sub_coercion.into()),
                    C(src_cmp_coercion.into()),
                    C(dst_cmp_coercion.into()),
                ]
                .to_lean(self),
            ),
        };
        let tactics = self.alloc_tactics([LnMirTacticData::Custom {
            name: litnum_bound_tactic_name_from_variant_name(variant_name).into(),
            arguments,
            construction: None,
        }]);
        self.alloc_expr(LnMirExprEntry::new(LnMirExprData::By { tactics }))
    }

    pub(super) fn build_litnum_bound_derivation_chunk_end_tactic_data(
        &mut self,
        construction: &VdMirLitnumBoundDerivationConstruction,
    ) -> LnMirTacticData {
        match construction {
            VdMirLitnumBoundDerivationConstruction::Finish { .. } => LnMirTacticData::Assumption,
            _ => todo!(),
        }
    }
}

fn litnum_bound_tactic_name_from_variant_name(variant_name: &'static str) -> String {
    format!(
        "litnum_bound_derivation_{}",
        variant_name.to_case(Case::Snake)
    )
}
