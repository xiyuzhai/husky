pub(crate) use expect_test::{expect, Expect};

use crate::*;

#[salsa::db(Jar)]
pub(crate) struct DB {}
