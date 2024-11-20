#[salsa::jar]
pub struct VdItemPathJar(crate::module::VdModulePath, crate::menu::vd_item_path_menu);
