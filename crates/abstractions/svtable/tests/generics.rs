use svtable::svtable;

#[svtable]
trait TestTrait<T: Clone, U> {
    fn assoc_fn1(x: T) -> T;
    fn assoc_fn2(s: &str, u: U) -> String;
    fn assoc_fn3(t: T, u: U);
}

struct TestStruct;

impl TestTrait<i32, String> for TestStruct {
    fn assoc_fn1(x: i32) -> i32 {
        x * 2
    }

    fn assoc_fn2(s: &str, u: String) -> String {
        format!("{}{}", s.to_uppercase(), u)
    }

    fn assoc_fn3(t: i32, u: String) {
        println!("Associated function 3 called with {} and {}", t, u);
    }
}

#[test]
fn test_svtable_creation() {
    let vtable = TestTraitSvtable::<i32, String>::new::<TestStruct>();

    // Test assoc_fn1
    assert_eq!((vtable.assoc_fn1)(5), 10);

    // Test assoc_fn2
    assert_eq!(
        (vtable.assoc_fn2)("hello", "world".to_string()),
        "HELLOworld"
    );

    // Test assoc_fn3 (we can only test that it doesn't panic)
    (vtable.assoc_fn3)(42, "test".to_string());
}

#[test]
fn test_svtable_type_safety() {
    fn accepts_test_trait(_: &TestTraitSvtable<i32, String>) {}

    let svtable = TestTraitSvtable::<i32, String>::new::<TestStruct>();
    accepts_test_trait(&svtable);
}

#[test]
fn test_svtable_multiple_implementations() {
    struct AnotherStruct;

    impl TestTrait<String, Vec<i32>> for AnotherStruct {
        fn assoc_fn1(x: String) -> String {
            x.chars().rev().collect()
        }

        fn assoc_fn2(s: &str, u: Vec<i32>) -> String {
            format!("{}: {:?}", s, u)
        }

        fn assoc_fn3(t: String, u: Vec<i32>) {
            println!(
                "AnotherStruct's associated function 3 called with {} and {:?}",
                t, u
            );
        }
    }

    let vtable1 = TestTraitSvtable::<i32, String>::new::<TestStruct>();
    let vtable2 = TestTraitSvtable::<String, Vec<i32>>::new::<AnotherStruct>();

    assert_eq!((vtable1.assoc_fn1)(5), 10);
    assert_eq!((vtable2.assoc_fn1)("hello".to_string()), "olleh");

    assert_eq!(
        (vtable1.assoc_fn2)("hello", "world".to_string()),
        "HELLOworld"
    );
    assert_eq!(
        (vtable2.assoc_fn2)("numbers", vec![1, 2, 3]),
        "numbers: [1, 2, 3]"
    );

    // Again, we can only test that these don't panic
    (vtable1.assoc_fn3)(42, "test".to_string());
    (vtable2.assoc_fn3)("test".to_string(), vec![4, 5, 6]);
}
