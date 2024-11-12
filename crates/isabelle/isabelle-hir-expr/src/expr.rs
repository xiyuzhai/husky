use idx_arena::{Arena, ArenaIdx, ArenaIdxRange};

pub enum IeHirExprData {
    // Add variants here as needed
}

pub type IeHirExprArena = Arena<IeHirExprData>;
pub type IeHirExprIdx = ArenaIdx<IeHirExprData>;
pub type IeHirExprIdxRange = ArenaIdxRange<IeHirExprData>;
