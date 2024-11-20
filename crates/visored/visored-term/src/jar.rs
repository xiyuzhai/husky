#[salsa::jar]
pub struct VdTermJar(
    crate::ty::VdType,
    crate::ty::is_vd_ty_function_like,
    crate::term::VdTermId,
    crate::term::literal::zfc_literal_ty,
    crate::term::zfc_term_to_ty,
    crate::term::menu::vd_term_menu,
    crate::menu::vd_ty_menu,
    crate::instantiation::VdInstantiation,
    crate::instantiation::menu::vd_instantiation_menu,
);
