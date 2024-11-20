pub mod menu;

use crate::term::LnTerm;
use lean_item_path::LnItemPath;
use smallvec::*;

#[salsa::interned]
pub struct LnInstantiation {
    pub item_path: LnItemPath,
    #[return_ref]
    pub arguments: SmallVec<[LnTerm; 2]>,
}
