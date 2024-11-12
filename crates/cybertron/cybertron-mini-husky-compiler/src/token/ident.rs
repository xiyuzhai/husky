use husky_wild_utils::arb_ref;
use lazy_static::lazy_static;
use shifted_unsigned_int::ShiftedU32;
use std::{collections::HashMap, ops::Deref, sync::RwLock};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ident(ShiftedU32);

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "`{}`", self.repr())
    }
}

#[derive(Default)]
pub struct IdentStorage {
    data: Vec<String>,
    ids: HashMap<String, ShiftedU32>,
}

lazy_static! {
    static ref IDENT_STORAGE: RwLock<IdentStorage> = Default::default();
}

impl Ident {
    pub fn new(s: impl Into<String>) -> Self {
        let s = s.into();
        let mut guard = IDENT_STORAGE.write().unwrap();
        match guard.ids.get(&s) {
            Some(&id) => Self(id),
            None => {
                let id = ShiftedU32::from(guard.data.len());
                guard.ids.insert(s.clone(), id);
                guard.data.push(s);
                Self(id)
            }
        }
    }
}

impl Ident {
    pub fn repr(self) -> &'static str {
        let guard = IDENT_STORAGE.read().unwrap();
        unsafe { arb_ref(&guard.data[self.0.index()]) }
    }
}

#[test]
fn ident_works() {
    let a = Ident::new("hello");
    assert_eq!(a.repr(), "hello");
    let b = Ident::new("2");
    assert_eq!(b.repr(), "2");
    assert_ne!(a, b);
    let c = Ident::new("hello");
    assert_eq!(c.repr(), "hello");
    assert_eq!(a, c);
}
