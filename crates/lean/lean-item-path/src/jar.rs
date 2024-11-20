#[salsa::jar]
pub struct LnItemPathJar(
    crate::menu::ln_item_path_menu,
    crate::namespace::LnNamespace,
    crate::namespace::ln_namespace_all_idents,
);
