pub(crate) use expect_test::*;
pub(crate) use salsa::DebugWithDb;

use husky_coword::jar::CowordJar;

#[salsa::db(
    CowordJar,
    crate::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar
)]
pub struct DB {}
