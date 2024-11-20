#[salsa::jar]
pub struct LnTermJar(
    crate::term::LnTermId,
    crate::instantiation::LnInstantiation,
    crate::instantiation::menu::ln_instantiation_menu,
    crate::menu::ln_term_menu,
);
