use crate::data::entry::NamEntryAstData;

#[salsa::input]
pub struct NamAstDistrict {
    #[return_ref]
    data: NamEntryAstData,
}
