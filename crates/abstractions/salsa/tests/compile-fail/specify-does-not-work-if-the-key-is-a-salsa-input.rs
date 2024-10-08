//! Test that `specify` does not work if the key is a `salsa::input`
//! compilation fails
#![allow(warnings)]

#[salsa::jar]
struct Jar(MyInput, MyTracked, tracked_fn);

#[salsa::input(jar = Jar)]
struct MyInput {
    field: u32,
}

#[salsa::tracked(jar = Jar)]
struct MyTracked {
    field: u32,
}

#[salsa::tracked(jar = Jar, specify)]
fn tracked_fn(db: &Db, input: MyInput) -> MyTracked {
    MyTracked::new(db, input.field(db) * 2)
}

#[salsa::db(Jar)]
#[derive(Default)]
struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}

impl Db for Database {}

fn main() {}
