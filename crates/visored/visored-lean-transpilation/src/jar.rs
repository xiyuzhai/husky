#[salsa::jar]
pub struct VdLeanTranspilationJar(crate::expr::to_lean_literal);
