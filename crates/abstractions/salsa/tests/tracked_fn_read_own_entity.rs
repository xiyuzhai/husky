//! Test that a `tracked` fn on a `salsa::input`
//! compiles and executes successfully.

use expect_test::expect;
use husky_salsa_log_utils::HasLogger;
use salsa::Db;
use test_log::test;

#[salsa::jar]
struct Jar(MyInput, MyTracked, final_result, intermediate_result);

#[salsa::input(db = Db, jar = Jar)]
struct MyInput {
    field: u32,
}

#[salsa::tracked(jar = Jar)]
fn final_result(db: &Db, input: MyInput) -> u32 {
    db.push_log(format!("final_result({:?})", input));
    intermediate_result(db, input).field(db) * 2
}

#[salsa::tracked(db = Db, jar = Jar)]
struct MyTracked {
    field: u32,
}

#[salsa::tracked(jar = Jar)]
fn intermediate_result(db: &Db, input: MyInput) -> MyTracked {
    db.push_log(format!("intermediate_result({:?})", input));
    let tracked = MyTracked::new(db, input.field(db) / 2);
    let _ = tracked.field(db); // read the field of an entity we created
    tracked
}

#[salsa::db(Jar)]
struct Database;

#[test]
fn one_entity() {
    let mut db = Database::default();

    let input = MyInput::new(&db, 22, salsa::Durability::LOW);
    assert_eq!(final_result(&db, input), 22);
    db.assert_logs(expect![[r#"
        [
            "final_result(MyInput(Id { value: 1 }))",
            "intermediate_result(MyInput(Id { value: 1 }))",
        ]"#]]);

    // Intermediate result is the same, so final result does
    // not need to be recomputed:
    input.set_field(salsa::Durability::LOW, &mut db).to(23);
    assert_eq!(final_result(&db, input), 22);
    db.assert_logs(expect![[r#"
        [
            "intermediate_result(MyInput(Id { value: 1 }))",
        ]"#]]);

    input.set_field(salsa::Durability::LOW, &mut db).to(24);
    assert_eq!(final_result(&db, input), 24);
    db.assert_logs(expect![[r#"
        [
            "intermediate_result(MyInput(Id { value: 1 }))",
            "final_result(MyInput(Id { value: 1 }))",
        ]"#]]);
}

/// Create and mutate a distinct input. No re-execution required.
#[test]
fn red_herring() {
    let mut db = Database::default();

    let input = MyInput::new(&db, 22, salsa::Durability::LOW);
    assert_eq!(final_result(&db, input), 22);
    db.assert_logs(expect![[r#"
        [
            "final_result(MyInput(Id { value: 1 }))",
            "intermediate_result(MyInput(Id { value: 1 }))",
        ]"#]]);

    // Create a distinct input and mutate it.
    // This will trigger a new revision in the database
    // but shouldn't actually invalidate our existing ones.
    let input2 = MyInput::new(&db, 44, salsa::Durability::LOW);
    input2.set_field(salsa::Durability::LOW, &mut db).to(66);

    // Re-run the query on the original input. Nothing re-executes!
    assert_eq!(final_result(&db, input), 22);
    db.assert_logs(expect![[r#"
        []"#]]);
}
