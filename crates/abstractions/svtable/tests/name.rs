use svtable::svtable;

#[svtable(name=TestTraitSvtable)]
trait TestTrait {
    fn assoc_fn1(x: i32) -> i32;
    fn assoc_fn2(s: &str) -> String;
    fn assoc_fn3();
}

struct TestStruct;

impl TestTrait for TestStruct {
    fn assoc_fn1(x: i32) -> i32 {
        x * 2
    }

    fn assoc_fn2(s: &str) -> String {
        s.to_uppercase()
    }

    fn assoc_fn3() {
        println!("Associated function 3 called");
    }
}

#[test]
fn test_svtable_creation() {
    let vtable = TestTraitSvtable::new::<TestStruct>();

    // Test assoc_fn1
    assert_eq!((vtable.assoc_fn1)(5), 10);

    // Test assoc_fn2
    assert_eq!((vtable.assoc_fn2)("hello"), "HELLO");

    // Test assoc_fn3 (we can only test that it doesn't panic)
    (vtable.assoc_fn3)();
}

#[test]
fn test_svtable_type_safety() {
    fn accepts_test_trait(_: &TestTraitSvtable) {}

    let vtable = TestTraitSvtable::new::<TestStruct>();
    accepts_test_trait(&vtable);
}

#[test]
fn test_svtable_multiple_implementations() {
    struct AnotherStruct;

    impl TestTrait for AnotherStruct {
        fn assoc_fn1(x: i32) -> i32 {
            x * 3
        }

        fn assoc_fn2(s: &str) -> String {
            s.chars().rev().collect()
        }

        fn assoc_fn3() {
            println!("AnotherStruct's associated function 3 called");
        }
    }

    let vtable1 = TestTraitSvtable::new::<TestStruct>();
    let vtable2 = TestTraitSvtable::new::<AnotherStruct>();

    assert_eq!((vtable1.assoc_fn1)(5), 10);
    assert_eq!((vtable2.assoc_fn1)(5), 15);

    assert_eq!((vtable1.assoc_fn2)("hello"), "HELLO");
    assert_eq!((vtable2.assoc_fn2)("hello"), "olleh");

    // Again, we can only test that these don't panic
    (vtable1.assoc_fn3)();
    (vtable2.assoc_fn3)();
}
