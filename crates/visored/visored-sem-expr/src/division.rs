pub mod helpers;
#[cfg(test)]
mod tests;

use crate::stmt::VdSemStmtIdxRange;
use crate::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_token::idx::LxRoseTokenIdx;
use visored_item_path::module::VdModulePath;
use visored_prelude::division::VdDivisionLevel;
use visored_syn_expr::division::{VdSynDivisionData, VdSynDivisionIdx, VdSynDivisionIdxRange};

pub struct VdSemDivisionEntry {
    data: VdSemDivisionData,
    module_path: VdModulePath,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemDivisionData {
    Stmts {
        stmts: VdSemStmtIdxRange,
    },
    Divisions {
        command_token_idx: LxRoseTokenIdx,
        level: VdDivisionLevel,
        lcurl_token_idx: LxRoseTokenIdx,
        rcurl_token_idx: LxRoseTokenIdx,
        subdivisions: VdSemDivisionIdxRange,
    },
}

pub type VdSemDivisionArena = Arena<VdSemDivisionEntry>;
pub type VdSemDivisionArenaRef<'a> = ArenaRef<'a, VdSemDivisionEntry>;
pub type VdSemDivisionMap<T> = ArenaMap<VdSemDivisionEntry, T>;
pub type VdSemDivisionIdx = ArenaIdx<VdSemDivisionEntry>;
pub type VdSemDivisionIdxRange = ArenaIdxRange<VdSemDivisionEntry>;

impl VdSemDivisionEntry {
    pub fn new(data: VdSemDivisionData, module_path: VdModulePath) -> Self {
        Self { data, module_path }
    }
}

impl VdSemDivisionEntry {
    pub fn data(&self) -> &VdSemDivisionData {
        &self.data
    }

    pub fn module_path(&self) -> VdModulePath {
        self.module_path
    }
}

impl ToVdSem<VdSemDivisionIdxRange> for VdSynDivisionIdxRange {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemDivisionIdxRange {
        let mut divisions: Vec<VdSemDivisionEntry> = vec![];
        for division in self {
            let module_path = builder.division_entity_tree_node_map()[division].module_path();
            divisions.push(VdSemDivisionEntry::new(
                builder.build_division(division),
                module_path,
            ));
        }
        builder.alloc_divisions(divisions)
    }
}

impl<'a> VdSemExprBuilder<'a> {
    pub(crate) fn build_division(&mut self, division: VdSynDivisionIdx) -> VdSemDivisionData {
        match self.syn_division_arena()[division] {
            VdSynDivisionData::Stmts { stmts } => VdSemDivisionData::Stmts {
                stmts: stmts.to_vd_sem(self),
            },
            VdSynDivisionData::Divisions {
                command_token_idx,
                level,
                lcurl_token_idx,
                rcurl_token_idx,
                subdivisions,
            } => VdSemDivisionData::Divisions {
                command_token_idx,
                level,
                lcurl_token_idx,
                rcurl_token_idx,
                subdivisions: subdivisions.to_vd_sem(self),
            },
        }
    }
}
