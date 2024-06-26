pub mod connection;
pub mod form;
pub mod trai;
pub mod ty;
mod utils;

use self::connection::*;
use self::form::*;
use self::trai::*;
use self::ty::*;
use super::*;
use utils::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum MajorItemPath {
    Type(TypePath),
    Trait(TraitPath),
    Form(MajorFormPath),
}

impl std::ops::Deref for MajorItemPath {
    type Target = ItemPathId;

    fn deref(&self) -> &Self::Target {
        unsafe { &std::mem::transmute::<_, &(u32, ItemPathId)>(self).1 }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum MajorItemPathData {
    Type(TypePathData),
    Trait(TraitPathData),
    Form(FormPathData),
}

impl MajorItemPath {
    pub fn data(self, db: &::salsa::Db) -> MajorItemPathData {
        match (*self).data(db) {
            ItemPathData::MajorItem(data) => data,
            _ => unreachable!(),
        }
    }

    pub fn ty_path(self) -> Option<TypePath> {
        match self {
            MajorItemPath::Type(data) => Some(data),
            MajorItemPath::Trait(_) | MajorItemPath::Form(_) => None,
        }
    }

    pub fn ident(self, db: &::salsa::Db) -> Ident {
        self.data(db).ident()
    }
}

impl MajorItemPathData {
    #[inline(always)]
    pub(super) fn item_path(self, id: ItemPathId) -> MajorItemPath {
        match self {
            MajorItemPathData::Type(slf) => slf.item_path(id).into(),
            MajorItemPathData::Trait(slf) => slf.item_path(id).into(),
            MajorItemPathData::Form(slf) => slf.item_path(id).into(),
        }
    }

    pub fn module_path(self, _db: &::salsa::Db) -> ModulePath {
        match self {
            MajorItemPathData::Type(data) => data.module_path(),
            MajorItemPathData::Trait(data) => data.module_path(),
            MajorItemPathData::Form(data) => data.module_path(),
        }
    }
    pub fn ident(self) -> Ident {
        match self {
            MajorItemPathData::Type(data) => data.ident(),
            MajorItemPathData::Trait(data) => data.ident(),
            MajorItemPathData::Form(data) => data.ident(),
        }
    }

    pub fn crate_path(self, db: &::salsa::Db) -> CratePath {
        self.module_path(db).crate_path(db)
    }

    pub(crate) fn entity_kind(self, _db: &::salsa::Db) -> EntityKind {
        match self {
            MajorItemPathData::Type(data) => data.item_kind(),
            MajorItemPathData::Trait(data) => EntityKind::MajorItem {
                module_item_kind: MajorItemKind::Trait,
                connection: data.connection().kind(),
            },
            MajorItemPathData::Form(data) => EntityKind::MajorItem {
                module_item_kind: MajorItemKind::Form(data.form_kind()),
                connection: data.connection().kind(),
            },
        }
    }
}

impl salsa::DisplayWithDb for MajorItemPath {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        match self {
            MajorItemPath::Form(path) => path.display_fmt_with_db(f, db),
            MajorItemPath::Type(path) => path.display_fmt_with_db(f, db),
            MajorItemPath::Trait(path) => path.display_fmt_with_db(f, db),
        }
    }
}
