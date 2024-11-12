use crate::{expr::VdHirExprIdx, *};
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use visored_sem_expr::stmt::VdSemStmtIdxRange;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VdHirStmtData {
    // Add appropriate variants here, for example:
    Expression(VdHirExprIdx),
    Block(VdHirStmtIdxRange),
    // Add more variants as needed
}

pub type VdHirStmtArena = Arena<VdHirStmtData>;
pub type VdHirStmtArenaRef<'a> = ArenaRef<'a, VdHirStmtData>;
pub type VdHirStmtIdx = ArenaIdx<VdHirStmtData>;
pub type VdHirStmtIdxRange = ArenaIdxRange<VdHirStmtData>;

impl ToVdHir<VdHirStmtIdxRange> for VdSemStmtIdxRange {
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> VdHirStmtIdxRange {
        todo!()
    }
}
