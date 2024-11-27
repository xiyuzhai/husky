use crate::*;
use interned::memo;
use lean_coword::ident::LnIdent;
use smallvec::{smallvec, SmallVec, ToSmallVec};

#[interned::interned(override_debug)]
pub struct LnNamespace {
    pub data: LnNamespaceData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LnNamespaceData {
    Root,
    Child(LnNamespace, LnIdent),
}

impl LnNamespace {
    pub fn new_root() -> Self {
        Self::new(LnNamespaceData::Root)
    }

    pub fn from_ident_strs(idents: &[&str]) -> Self {
        let mut namespace = LnNamespace::new(LnNamespaceData::Root);
        for ident in idents {
            namespace = namespace.child(ident.to_string());
        }
        namespace
    }

    pub fn child(self, ident: String) -> Self {
        Self::new(LnNamespaceData::Child(self, LnIdent::from_owned(ident)))
    }

    pub fn ident(self) -> Option<LnIdent> {
        match *self.data() {
            LnNamespaceData::Root => None,
            LnNamespaceData::Child(_, ident) => Some(ident),
        }
    }

    pub fn all_idents(self) -> &'static [LnIdent] {
        ln_namespace_all_idents(self)
    }

    pub fn relative_idents(self, other: Self) -> &'static [LnIdent] {
        let ids = self.all_idents();
        let other_ids = other.all_idents();
        let i = ids
            .iter()
            .zip(other_ids.iter())
            .position(|(a, b)| a != b)
            .unwrap_or(ids.len().min(other_ids.len()));
        &ids[i..]
    }
}

impl std::fmt::Debug for LnNamespace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "LnNamespace(`{}`)",
            self.all_idents()
                .iter()
                .map(|id| id.data())
                .collect::<Vec<_>>()
                .join(".")
        )
    }
}

#[memo]
fn ln_namespace_all_idents(namespace: LnNamespace) -> SmallVec<[LnIdent; 4]> {
    match *namespace.data() {
        LnNamespaceData::Root => smallvec![],
        LnNamespaceData::Child(parent, ident) => {
            let mut ids = parent.all_idents().to_smallvec();
            ids.push(ident);
            ids
        }
    }
}

// #[test]
// #[ignore]
// fn ln_namespace_all_idents_works() {
//     fn t(idents: &[&str]) {
//         let namespace = LnNamespace::from_ident_strs(idents);
//         let all_idents: Vec<&str> = namespace
//             .all_idents()
//             .iter()
//             .map(|&ident| ident.data())
//             .collect();
//         assert_eq!(&all_idents as &[_], idents);
//     }
//     t(&["Root"]);
//     t(&["Root", "Child"]);
//     t(&["Root", "Child", "Grandchild"]);
// }

// #[test]
// #[ignore]
// fn ln_namespace_relative_idents_works() {
//     fn t(slf: &[&str], other: &[&str], relative_idents: &[&str]) {
//         let slf = LnNamespace::from_ident_strs(slf);
//         let other = LnNamespace::from_ident_strs(other);
//         assert_eq!(
//             slf.relative_idents(other,)
//                 .iter()
//                 .map(|&ident| ident.data())
//                 .collect::<Vec<_>>(),
//             relative_idents,
//             "slf: {slf:?}, other: {other:?}",
//         );
//     }
//     t(&["Root"], &["Root"], &[]);
//     t(&["Root"], &["Root", "Child"], &[]);
//     t(&["Root", "Child"], &["Root", "Child", "Grandchild"], &[]);
//     t(
//         &["Root", "Child", "Grandchild"],
//         &["Root", "Child"],
//         &["Grandchild"],
//     );
// }
