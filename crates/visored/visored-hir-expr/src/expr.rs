pub mod application;
#[cfg(test)]
pub mod tests;

use crate::*;
use application::VdHirApplicationFunction;
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use visored_global_resolution::resolution::letter::VdLetterGlobalResolution;
use visored_item_path::path::VdItemPath;
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_sem_expr::expr::{
    binary::VdSemBinaryDispatch, letter::VdSemLetterDispatch,
    separated_list::VdSemSeparatedListDispatch, VdSemExprData, VdSemExprIdx, VdSemExprIdxRange,
};
use visored_zfc_ty::term::literal::VdZfcLiteral;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VdHirExprData {
    Literal(VdZfcLiteral),
    Variable(VdHirVariable),
    Application {
        function: VdHirApplicationFunction,
        arguments: VdHirExprIdxRange,
    },
    ItemPath(VdItemPath),
}

pub type VdHirExprArena = Arena<VdHirExprData>;
pub type VdHirExprArenaRef<'a> = ArenaRef<'a, VdHirExprData>;
pub type VdHirExprIdx = ArenaIdx<VdHirExprData>;
pub type VdHirExprIdxRange = ArenaIdxRange<VdHirExprData>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdHirLiteral {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdHirVariable {}

impl ToVdHir<VdHirExprIdxRange> for VdSemExprIdxRange {
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> VdHirExprIdxRange {
        let mut exprs: Vec<VdHirExprData> = Vec::with_capacity(self.len());
        for expr in self {
            exprs.push(builder.build_expr(expr));
        }
        builder.alloc_exprs(exprs)
    }
}

impl ToVdHir<VdHirExprIdx> for VdSemExprIdx {
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> VdHirExprIdx {
        let data = builder.build_expr(self);
        builder.alloc_expr(data)
    }
}

impl<const N: usize> ToVdHir<VdHirExprIdxRange> for [VdSemExprIdx; N] {
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> VdHirExprIdxRange {
        let data = self
            .into_iter()
            .map(|expr| builder.build_expr(expr))
            .collect::<Vec<_>>();
        builder.alloc_exprs(data)
    }
}

impl<'db> VdHirExprBuilder<'db> {
    fn build_expr(&mut self, sem_expr_idx: VdSemExprIdx) -> VdHirExprData {
        match self.sem_expr_arena()[sem_expr_idx] {
            VdSemExprData::Literal { literal, .. } => VdHirExprData::Literal(literal),
            VdSemExprData::Binary {
                lopd,
                opr,
                ropd,
                ref dispatch,
            } => VdHirExprData::Application {
                function: match dispatch {
                    VdSemBinaryDispatch::IntAdd => VdHirApplicationFunction::IntAdd,
                    VdSemBinaryDispatch::TrivialEq => VdHirApplicationFunction::TrivialEq,
                },
                arguments: [lopd, ropd].to_vd_hir(self),
            },
            VdSemExprData::Prefix {
                opr,
                opd,
                ref dispatch,
            } => todo!(),
            VdSemExprData::Suffix {
                opd,
                opr,
                ref dispatch,
            } => todo!(),
            VdSemExprData::Attach { .. } => todo!(),
            VdSemExprData::UniadicChain => todo!(),
            VdSemExprData::VariadicChain => todo!(),
            VdSemExprData::UniadicArray => todo!(),
            VdSemExprData::VariadicArray => todo!(),
            VdSemExprData::Letter {
                token_idx_range,
                letter,
                ref dispatch,
            } => match dispatch {
                VdSemLetterDispatch::Global(global_resolution) => match *global_resolution {
                    VdLetterGlobalResolution::Item(vd_item_path) => {
                        VdHirExprData::ItemPath(vd_item_path)
                    }
                },
                VdSemLetterDispatch::Local(local_defn) => VdHirExprData::Variable(VdHirVariable {}),
            },
            VdSemExprData::BaseOpr { opr } => todo!(),
            VdSemExprData::SeparatedList {
                items,
                ref dispatch,
                ..
            } => VdHirExprData::Application {
                function: match dispatch {
                    VdSemSeparatedListDispatch::IntAdd => VdHirApplicationFunction::IntAdd,
                    VdSemSeparatedListDispatch::Eq => VdHirApplicationFunction::TrivialEq,
                    VdSemSeparatedListDispatch::IntMul => todo!(),
                    VdSemSeparatedListDispatch::In => todo!(),
                },
                arguments: items.to_vd_hir(self),
            },
            VdSemExprData::LxDelimited { item, .. } | VdSemExprData::Delimited { item, .. } => {
                self.build_expr(item)
            }
            VdSemExprData::Fraction {
                numerator,
                denominator,
                ..
            } => todo!(),
            VdSemExprData::Sqrt {
                command_token_idx,
                radicand_lcurl_token_idx,
                radicand,
                radicand_rcurl_token_idx,
            } => todo!(),
        }
    }
}
