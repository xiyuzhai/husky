#[interned::interned]
pub struct Coword {
    pub data: String,
}

impl std::fmt::Debug for Coword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Coword").field(self.data()).finish()
    }
}

#[test]
fn coword_new_works() {
    // Test creation and basic equality
    let word1 = Coword::new("hello".to_string());
    let word2 = Coword::new("hello".to_string());
    let word3 = Coword::new("world".to_string());

    // Test equality for same content
    assert_eq!(word1, word2);

    // Test inequality for different content
    assert_ne!(word1, word3);

    // Test interning - should return same instance for same content
    assert_eq!(word1, word2);
    assert_ne!(word1, word3);

    // Test access to underlying data
    assert_eq!(word1.data(), "hello");
    assert_eq!(word3.data(), "world");
}

#[test]
fn coword_from_ref_works() {
    // Test creation and basic equality
    let word1 = Coword::from_ref("hello");
    let word2 = Coword::from_ref("hello");
    let word3 = Coword::from_ref("world");

    // Test equality for same content
    assert_eq!(word1, word2);

    // Test inequality for different content
    assert_ne!(word1, word3);

    // Test interning - should return same instance for same content
    assert_eq!(word1, word2);
    assert_ne!(word1, word3);

    // Test access to underlying data
    assert_eq!(word1.data(), "hello");
    assert_eq!(word3.data(), "world");
}
