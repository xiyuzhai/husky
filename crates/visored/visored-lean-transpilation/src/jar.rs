#[salsa::jar]
pub struct VdLeanTranspilationJar(
    crate::expr::to_lean_literal,
    crate::namespace::vd_module_path_to_ln_namespace,
    crate::namespace::vd_module_path_to_ln_namespace_or_inherited,
);
