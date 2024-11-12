pub(crate) use expect_test::*;
pub(crate) use salsa::DebugWithDb;

use husky_coword::jar::CowordJar;

#[salsa::db(CowordJar)]
pub struct DB {}
