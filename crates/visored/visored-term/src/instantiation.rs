pub mod menu;

use crate::term::VdTerm;
use smallvec::SmallVec;
use visored_item_path::path::VdItemPath;

#[salsa::interned]
pub struct VdInstantiation {
    pub path: VdItemPath,
    #[return_ref]
    pub arguments: SmallVec<[VdTerm; 4]>,
}
