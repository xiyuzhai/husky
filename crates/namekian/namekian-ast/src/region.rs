use self::data::entry::NamEntryAstData;
use crate::*;

#[salsa::tracked]
pub struct NamAstRegion {
    #[return_ref]
    data: NamEntryAstData,
}
