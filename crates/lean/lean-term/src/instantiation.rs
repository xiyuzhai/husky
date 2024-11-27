pub mod menu;

use crate::term::LnTerm;
use lean_entity_path::LnItemPath;
use smallvec::*;

#[interned::interned]
pub struct LnInstantiation {
    pub item_path: LnItemPath,
    #[return_ref]
    pub arguments: SmallVec<[LnTerm; 2]>,
}

impl std::fmt::Debug for LnInstantiation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}...", self.item_path())
    }
}
