#[salsa::jar]
pub struct NamAstJar(crate::district::NamAstDistrict, crate::region::NamAstRegion);
