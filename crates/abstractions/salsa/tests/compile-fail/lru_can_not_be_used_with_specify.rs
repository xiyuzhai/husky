#[salsa::jar]
struct Jar(MyInput, lru_can_not_be_used_with_specify);

#[salsa::input(jar = Jar)]
struct MyInput {
    field: u32,
}

#[salsa::tracked(jar = Jar, lru = 3, specify)]
fn lru_can_not_be_used_with_specify(db: &Db, input: MyInput) -> u32 {
    input.field(db)
}

fn main() {}
