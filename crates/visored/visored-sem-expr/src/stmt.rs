#[cfg(test)]
mod tests;

use crate::sentence::VdSemSentenceIdxRange;
use crate::*;
use husky_coword::Coword;
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use latex_environment::signature::LxEnvironmentSignature;
use latex_token::idx::LxRoseTokenIdx;
use sentence::VdSemSentenceIdx;
use visored_item_path::module::VdModulePath;
use visored_syn_expr::stmt::{VdSynStmtData, VdSynStmtIdx};

pub struct VdSemStmtEntry {
    data: VdSemStmtData,
    module_path: VdModulePath,
}

pub enum VdSemStmtData {
    Paragraph(VdSemSentenceIdxRange),
    Environment {
        begin_command_token_idx: LxRoseTokenIdx,
        environment_signature: LxEnvironmentSignature,
        stmts: VdSemStmtIdxRange,
        end_rcurl_token_idx: LxRoseTokenIdx,
    },
}

pub type VdSemStmtArena = Arena<VdSemStmtEntry>;
pub type VdSemStmtArenaRef<'a> = ArenaRef<'a, VdSemStmtEntry>;
pub type VdSemStmtIdx = ArenaIdx<VdSemStmtEntry>;
pub type VdSemStmtIdxRange = ArenaIdxRange<VdSemStmtEntry>;
pub type VdSemStmtMap<T> = ArenaMap<VdSemStmtEntry, T>;
pub type VdSemStmtOrderedMap<T> = ArenaOrderedMap<VdSemStmtEntry, T>;

impl VdSemStmtEntry {
    pub fn new(data: VdSemStmtData, module_path: VdModulePath) -> Self {
        Self { data, module_path }
    }
}

impl VdSemStmtEntry {
    pub fn data(&self) -> &VdSemStmtData {
        &self.data
    }

    pub fn module_path(&self) -> VdModulePath {
        self.module_path
    }
}

impl ToVdSem<VdSemStmtIdxRange> for VdSynStmtIdxRange {
    // there is no need to cache because stmts will be created in one go
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemStmtIdxRange {
        let mut stmts: Vec<VdSemStmtEntry> = vec![];
        for stmt in self {
            let module_path = builder.stmt_entity_tree_node_map()[stmt].module_path();
            stmts.push(VdSemStmtEntry::new(builder.build_stmt(stmt), module_path));
        }
        builder.alloc_stmts(stmts)
    }
}

impl<'a> VdSemExprBuilder<'a> {
    pub(crate) fn build_stmt(&mut self, stmt: VdSynStmtIdx) -> VdSemStmtData {
        match self.syn_stmt_arena()[stmt] {
            VdSynStmtData::Paragraph(sentences) => {
                VdSemStmtData::Paragraph(sentences.to_vd_sem(self))
            }
            VdSynStmtData::Environment {
                environment_signature,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => VdSemStmtData::Environment {
                environment_signature,
                stmts: stmts.to_vd_sem(self),
                begin_command_token_idx,
                end_rcurl_token_idx,
            },
        }
    }
}

pub enum VdSemStmtChild {
    Sentence(VdSemSentenceIdx),
    Stmt(VdSemStmtIdx),
}

impl VdSemStmtData {
    pub fn children(&self) -> Vec<VdSemStmtChild> {
        match *self {
            VdSemStmtData::Paragraph(sentences) => sentences
                .into_iter()
                .map(|s| VdSemStmtChild::Sentence(s))
                .collect(),
            VdSemStmtData::Environment {
                environment_signature,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => stmts.into_iter().map(|s| VdSemStmtChild::Stmt(s)).collect(),
        }
    }
}
