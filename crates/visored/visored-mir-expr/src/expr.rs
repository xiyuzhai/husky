pub mod application;
pub mod attach;
pub mod separated_list;
#[cfg(test)]
pub mod tests;

use crate::*;
use application::VdMirFunc;
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use smallvec::SmallVec;
use symbol::local_defn::VdMirSymbolLocalDefnIdx;
use visored_entity_path::path::VdItemPath;
use visored_global_dispatch::dispatch::{
    binary_opr::VdBinaryOprGlobalDispatch, prefix_opr::VdPrefixOprGlobalDispatch,
};
use visored_global_resolution::resolution::letter::VdLetterGlobalResolution;
use visored_opr::{
    opr::binary::VdBaseBinaryOpr,
    separator::{VdBaseSeparator, VdSeparatorClass},
};
use visored_sem_expr::expr::{
    binary::VdSemBinaryDispatch, frac::VdSemFracDispatch, letter::VdSemLetterDispatch,
    prefix::VdSemPrefixDispatch, separated_list::VdSemSeparatedListFollowerDispatch,
    sqrt::VdSemSqrtDispatch, VdSemExprData, VdSemExprIdx, VdSemExprIdxRange,
};
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;
use visored_term::{term::literal::VdLiteral, ty::VdType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VdMirExprData {
    Literal(VdLiteral),
    Variable(VdMirSymbolLocalDefnIdx),
    Application {
        function: VdMirFunc,
        arguments: VdMirExprIdxRange,
    },
    FoldingSeparatedList {
        leader: VdMirExprIdx,
        /// TODO: should we use VdBaseSeparatorSignature instead?
        followers: SmallVec<[(VdMirFunc, VdMirExprIdx); 4]>,
    },
    ChainingSeparatedList {
        leader: VdMirExprIdx,
        followers: SmallVec<[(VdMirFunc, VdMirExprIdx); 4]>,
        joined_separator_and_signature: Option<(VdBaseSeparator, VdBaseSeparatorSignature)>,
    },
    ItemPath(VdItemPath),
}

pub struct VdMirExprEntry {
    data: VdMirExprData,
    ty: VdType,
}

pub type VdMirExprArena = Arena<VdMirExprEntry>;
pub type VdMirExprMap<T> = ArenaMap<VdMirExprEntry, T>;
pub type VdMirExprOrderedMap<T> = ArenaOrderedMap<VdMirExprEntry, T>;
pub type VdMirExprArenaRef<'a> = ArenaRef<'a, VdMirExprEntry>;
pub type VdMirExprIdx = ArenaIdx<VdMirExprEntry>;
pub type VdMirExprIdxRange = ArenaIdxRange<VdMirExprEntry>;

impl VdMirExprEntry {
    pub fn data(&self) -> &VdMirExprData {
        &self.data
    }

    pub fn ty(&self) -> VdType {
        self.ty
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdMirLiteral {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdMirVariable {}

impl ToVdMir<VdMirExprIdxRange> for VdSemExprIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirExprIdxRange {
        let mut exprs: Vec<VdMirExprEntry> = Vec::with_capacity(self.len());
        for expr in self {
            exprs.push(builder.build_expr_entry(expr));
        }
        builder.alloc_exprs(exprs)
    }
}

impl ToVdMir<VdMirExprIdx> for VdSemExprIdx {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirExprIdx {
        let entry = builder.build_expr_entry(self);
        builder.alloc_expr(entry)
    }
}

impl<const N: usize> ToVdMir<VdMirExprIdxRange> for [VdSemExprIdx; N] {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirExprIdxRange {
        let entries = self
            .into_iter()
            .map(|expr| builder.build_expr_entry(expr))
            .collect::<Vec<_>>();
        builder.alloc_exprs(entries)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_expr_entry(&mut self, sem_expr_idx: VdSemExprIdx) -> VdMirExprEntry {
        let data = self.build_expr_data(sem_expr_idx);
        let ty = self.sem_expr_arena()[sem_expr_idx].ty();
        VdMirExprEntry { data, ty }
    }

    fn build_expr_data(&mut self, sem_expr_idx: VdSemExprIdx) -> VdMirExprData {
        match *self.sem_expr_arena()[sem_expr_idx].data() {
            VdSemExprData::Literal { literal, .. } => VdMirExprData::Literal(literal),
            VdSemExprData::Binary {
                lopd,
                opr,
                ropd,
                dispatch,
            } => VdMirExprData::Application {
                function: match dispatch {
                    VdSemBinaryDispatch::Global(global_dispatch) => match global_dispatch {
                        VdBinaryOprGlobalDispatch::Normal {
                            base_binary_opr,
                            signature,
                        } => VdMirFunc::NormalBaseBinaryOpr(signature),
                    },
                    // VdSemBinaryDispatch::IntAdd => VdMirApplicationFunction::IntAdd,
                    // VdSemBinaryDispatch::TrivialEq => VdMirApplicationFunction::TrivialEq,
                },
                arguments: [lopd, ropd].to_vd_mir(self),
            },
            VdSemExprData::Prefix { opr, opd, dispatch } => match dispatch {
                VdSemPrefixDispatch::Global(dispatch) => match dispatch {
                    VdPrefixOprGlobalDispatch::Base {
                        base_opr,
                        signature,
                    } => VdMirExprData::Application {
                        function: VdMirFunc::NormalBasePrefixOpr(signature),
                        arguments: [opd].to_vd_mir(self),
                    },
                },
            },
            VdSemExprData::Suffix {
                opd,
                opr,
                ref dispatch,
            } => todo!(),
            VdSemExprData::Attach {
                base,
                ref scripts,
                dispatch,
            } => self.build_attach(base, scripts, dispatch),
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
                        VdMirExprData::ItemPath(vd_item_path)
                    }
                },
                VdSemLetterDispatch::Local(local_defn) => {
                    VdMirExprData::Variable(local_defn.to_vd_mir(self))
                }
            },
            VdSemExprData::BaseOpr { opr } => todo!(),
            VdSemExprData::FoldingSeparatedList {
                separator_class,
                leader,
                ref followers,
                ..
            } => self.build_folding_separated_list(leader, followers),
            VdSemExprData::ChainingSeparatedList {
                separator_class,
                leader,
                ref followers,
                joined_separator_and_signature,
            } => self.build_chaining_separated_list(
                leader,
                followers,
                joined_separator_and_signature,
            ),
            VdSemExprData::LxDelimited { item, .. } | VdSemExprData::Delimited { item, .. } => {
                self.build_expr_data(item)
            }
            VdSemExprData::Frac {
                numerator,
                denominator,
                dispatch,
                ..
            } => match dispatch {
                VdSemFracDispatch::Div { signature } => VdMirExprData::Application {
                    function: VdMirFunc::NormalBaseFrac(signature),
                    arguments: [numerator, denominator].to_vd_mir(self),
                },
            },
            VdSemExprData::Sqrt {
                command_token_idx,
                radicand,
                dispatch,
                ..
            } => match dispatch {
                VdSemSqrtDispatch::Base { signature } => VdMirExprData::Application {
                    function: VdMirFunc::NormalBaseSqrt(signature),
                    arguments: [radicand].to_vd_mir(self),
                },
            },
        }
    }
}
