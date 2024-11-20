use crate::*;

#[salsa::db(husky_coword::jar::CowordJar, latex_vfs::jar::LxVfsJar, Jar)]
pub struct DB;
