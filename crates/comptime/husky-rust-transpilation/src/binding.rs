use crate::builder::{RustKeyword, RustPunctuation, TranspileToRust};
use smallvec::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RustBinding {
    Deref,
    DerefCustomed,
    Reref,
    RerefMut,
}

#[derive(Default)]
pub(crate) struct RustBindings {
    /// the order is the same as how it's written
    bindings: SmallVec<[RustBinding; 3]>,
}

impl std::ops::Deref for RustBindings {
    type Target = [RustBinding];

    fn deref(&self) -> &Self::Target {
        &self.bindings
    }
}

impl From<RustBinding> for RustBindings {
    fn from(binding: RustBinding) -> Self {
        Self {
            bindings: smallvec![binding],
        }
    }
}

impl RustBindings {
    pub(crate) fn push(&mut self, binding: RustBinding) {
        match self.bindings.last() {
            Some(last_binding) => match (last_binding, binding) {
                // the following is automatically coercible, so we can remove them
                // *&a -> a
                // *&mut a -> a
                // &*a -> a
                // &mut *a -> a
                (RustBinding::Deref, RustBinding::Reref | RustBinding::RerefMut)
                | (RustBinding::Reref | RustBinding::RerefMut, RustBinding::Deref) => {
                    self.bindings.pop();
                }
                (RustBinding::DerefCustomed, RustBinding::Reref | RustBinding::RerefMut) => {
                    unreachable!()
                }
                _ => self.bindings.push(binding),
            },
            None => self.bindings.push(binding),
        }
    }
}

#[test]
fn rust_bindings_works() {
    {
        // &*a -> a
        let mut bindings: RustBindings = RustBinding::Deref.into();
        bindings.push(RustBinding::Reref);
        assert!(bindings.is_empty())
    }
    {
        // &mut *a -> a
        let mut bindings: RustBindings = RustBinding::Deref.into();
        bindings.push(RustBinding::RerefMut);
        assert!(bindings.is_empty())
    }
    {
        // **a -> **a
        let mut bindings: RustBindings = RustBinding::Deref.into();
        bindings.push(RustBinding::Deref);
        assert_eq!(bindings.len(), 2)
    }
    {
        // &mut **a -> *a
        let mut bindings: RustBindings = RustBinding::Deref.into();
        bindings.push(RustBinding::Deref);
        bindings.push(RustBinding::RerefMut);
        assert_eq!(bindings.len(), 1)
    }
}

impl TranspileToRust for RustBinding {
    fn transpile_to_rust(&self, builder: &mut crate::builder::RustTranspilationBuilder<()>) {
        match self {
            RustBinding::Deref | RustBinding::DerefCustomed => {
                builder.punctuation(RustPunctuation::DerefStar)
            }
            RustBinding::Reref => builder.punctuation(RustPunctuation::Ambersand),
            RustBinding::RerefMut => {
                builder.punctuation(RustPunctuation::Ambersand);
                builder.keyword(RustKeyword::Mut)
            }
        }
    }
}

impl TranspileToRust for RustBindings {
    fn transpile_to_rust(&self, builder: &mut crate::builder::RustTranspilationBuilder<()>) {
        self.bindings.transpile_to_rust(builder)
    }
}