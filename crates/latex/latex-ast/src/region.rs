use crate::ast::LxAstArena;

#[salsa::tracked]
pub struct LxAstRegion {}

pub struct LxAstRegionData {
    arena: LxAstArena,
}

impl LxAstRegionData {
    pub(crate) fn new(arena: LxAstArena) -> Self {
        Self { arena }
    }
}

impl LxAstRegionData {
    pub fn arena(&self) -> &LxAstArena {
        &self.arena
    }
}
