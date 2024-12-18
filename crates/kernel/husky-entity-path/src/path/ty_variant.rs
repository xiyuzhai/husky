use super::{major_item::ty::TypePath, *};
use rustc_index::Idx;

#[salsa::as_id(jar = EntityPathJar)]
#[salsa::deref_id]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct TypeVariantPath(ItemPathId);

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct TypeVariantPathData {
    pub parent_ty_path: TypePath,
    pub ident: Ident,
    pub index: TypeVariantIndex,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct TypeVariantIndex(usize);

impl Idx for TypeVariantIndex {
    fn new(idx: usize) -> Self {
        Self(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

impl TypeVariantIndex {
    pub fn raw(self) -> usize {
        self.0
    }
}

pub struct TypeVariantRegistry {
    next_index: TypeVariantIndex,
}

impl TypeVariantRegistry {
    pub fn new_u8() -> Self {
        Self {
            next_index: TypeVariantIndex(0),
        }
    }

    fn issue_next(&mut self) -> TypeVariantIndex {
        match self.next_index {
            TypeVariantIndex(ref mut next_raw) => {
                TypeVariantIndex(std::mem::replace(next_raw, *next_raw + 1))
            }
        }
    }
}

impl TypeVariantPath {
    pub fn new(
        parent_ty_path: TypePath,
        ident: Ident,
        db: &::salsa::Db,
        registry: &mut TypeVariantRegistry,
    ) -> Self {
        Self(ItemPathId::new(
            db,
            ItemPathData::TypeVariant(TypeVariantPathData {
                parent_ty_path,
                ident,
                index: registry.issue_next(),
            }),
        ))
    }

    pub fn data(self, db: &::salsa::Db) -> TypeVariantPathData {
        match self.0.data(db) {
            ItemPathData::TypeVariant(data) => data,
            _ => unreachable!(),
        }
    }

    pub fn parent_ty_path(self, db: &::salsa::Db) -> TypePath {
        self.data(db).parent_ty_path
    }

    pub fn ident(self, db: &::salsa::Db) -> Ident {
        self.data(db).ident
    }

    pub fn index(self, db: &::salsa::Db) -> TypeVariantIndex {
        self.data(db).index
    }

    #[inline(never)]
    pub fn show_aux(self, f: &mut std::fmt::Formatter<'_>, db: &::salsa::Db) -> std::fmt::Result {
        self.data(db).show_aux(f, db)
    }
}

impl TypeVariantPathData {
    #[inline(always)]
    pub(super) fn item_path(self, id: ItemPathId) -> TypeVariantPath {
        TypeVariantPath(id)
    }

    pub fn toolchain(self, db: &::salsa::Db) -> Toolchain {
        self.parent_ty_path.toolchain(db)
    }

    pub fn module_path(self, db: &::salsa::Db) -> ModulePath {
        self.parent_ty_path.module_path(db)
    }

    #[inline(never)]
    pub fn show_aux(self, f: &mut std::fmt::Formatter<'_>, db: &::salsa::Db) -> std::fmt::Result {
        self.parent_ty_path.show_aux(f, db)?;
        f.write_str("::")?;
        f.write_str(self.ident.data())
    }
}

impl salsa::DebugWithDb for TypeVariantPath {
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        let data = self.data(db);
        f.write_str("TypeVariantPath(`")?;
        data.show_aux(f, db)?;
        f.write_str("`)")
    }
}

impl salsa::DisplayWithDb for TypeVariantPath {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        self.show_aux(f, db)
    }
}
