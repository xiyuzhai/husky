use crate::*;

#[salsa::db(husky_coword::jar::CowordJar, Jar)]
pub struct DB;
