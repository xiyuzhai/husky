use crate::*;
use lean_coword::ident::LnIdent;
use smallvec::{smallvec, SmallVec, ToSmallVec};

#[salsa::interned(override_debug)]
pub struct LnNamespace {
    pub data: LnNamespaceData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LnNamespaceData {
    Root,
    Child(LnNamespace, LnIdent),
}

impl LnNamespace {
    pub fn new_root(db: &::salsa::Db) -> Self {
        Self::new(db, LnNamespaceData::Root)
    }

    pub fn from_ident_strs(idents: &[&str], db: &::salsa::Db) -> Self {
        let mut namespace = LnNamespace::new(db, LnNamespaceData::Root);
        for ident in idents {
            namespace = namespace.child(ident.to_string(), db);
        }
        namespace
    }

    pub fn child(self, ident: String, db: &::salsa::Db) -> Self {
        Self::new(
            db,
            LnNamespaceData::Child(self, LnIdent::from_owned(ident, db)),
        )
    }

    pub fn ident(self, db: &::salsa::Db) -> Option<LnIdent> {
        match self.data(db) {
            LnNamespaceData::Root => None,
            LnNamespaceData::Child(_, ident) => Some(ident),
        }
    }

    pub fn all_idents(self, db: &::salsa::Db) -> &[LnIdent] {
        ln_namespace_all_idents(db, self)
    }

    pub fn relative_idents(self, other: Self, db: &::salsa::Db) -> &[LnIdent] {
        let ids = self.all_idents(db);
        let other_ids = other.all_idents(db);
        let i = ids
            .iter()
            .zip(other_ids.iter())
            .position(|(a, b)| a != b)
            .unwrap_or(ids.len().min(other_ids.len()));
        &ids[i..]
    }
}

impl ::salsa::DebugWithDb for LnNamespace {
    fn debug_fmt_with_db(
        &self,
        f: &mut ::std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> ::std::fmt::Result {
        write!(
            f,
            "LnNamespace(`{}`)",
            self.all_idents(db)
                .iter()
                .map(|id| id.data(db))
                .collect::<Vec<_>>()
                .join(".")
        )
    }
}

#[salsa::tracked(return_ref)]
fn ln_namespace_all_idents(db: &::salsa::Db, namespace: LnNamespace) -> SmallVec<[LnIdent; 4]> {
    match namespace.data(db) {
        LnNamespaceData::Root => smallvec![],
        LnNamespaceData::Child(parent, ident) => {
            let mut ids = parent.all_idents(db).to_smallvec();
            ids.push(ident);
            ids
        }
    }
}

#[test]
fn ln_namespace_all_idents_works() {
    fn t(idents: &[&str]) {
        let db = &DB::default();
        let namespace = LnNamespace::from_ident_strs(idents, db);
        let all_idents: Vec<&str> = namespace
            .all_idents(db)
            .iter()
            .map(|&ident| ident.data(db))
            .collect();
        assert_eq!(&all_idents as &[_], idents);
    }
    t(&["Root"]);
    t(&["Root", "Child"]);
    t(&["Root", "Child", "Grandchild"]);
}

#[test]
fn ln_namespace_relative_idents_works() {
    fn t(slf: &[&str], other: &[&str], relative_idents: &[&str]) {
        use salsa::DebugWithDb;

        let db = &DB::default();
        let slf = LnNamespace::from_ident_strs(slf, db);
        let other = LnNamespace::from_ident_strs(other, db);
        assert_eq!(
            slf.relative_idents(other, db)
                .iter()
                .map(|&ident| ident.data(db))
                .collect::<Vec<_>>(),
            relative_idents,
            "slf: {:?}, other: {:?}",
            slf.debug(db),
            other.debug(db),
        );
    }
    t(&["Root"], &["Root"], &[]);
    t(&["Root"], &["Root", "Child"], &[]);
    t(&["Root", "Child"], &["Root", "Child", "Grandchild"], &[]);
    t(
        &["Root", "Child", "Grandchild"],
        &["Root", "Child"],
        &["Grandchild"],
    );
}
