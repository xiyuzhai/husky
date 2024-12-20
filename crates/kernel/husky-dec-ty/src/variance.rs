mod default;
mod dependency;
mod graph;
mod repr;

pub(crate) use dependency::*;
use husky_entity_path::path::{
    assoc_item::ty_item::TypeItemPath,
    major_item::{form::MajorFormPath, trai::TraitPath, ty::TypePath, MajorItemPath},
    ItemPath,
};
pub(crate) use repr::*;

use super::*;
use graph::*;
use propagate::*;

#[derive(Debug, PartialEq, Eq)]
pub enum VarianceError {
    Original(OriginalVarianceError),
    Derived(DerivedVarianceError),
}

impl From<DerivedVarianceError> for VarianceError {
    fn from(v: DerivedVarianceError) -> Self {
        Self::Derived(v)
    }
}

impl From<OriginalVarianceError> for VarianceError {
    fn from(v: OriginalVarianceError) -> Self {
        Self::Original(v)
    }
}

pub type VarianceResult<T> = Result<T, VarianceError>;
pub type VarianceResultRef<'a, T> = Result<T, &'a VarianceError>;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum OriginalVarianceError {
    Todo,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum DerivedVarianceError {
    SynDeclError,
    SignatureError,
    TypeItemNotFound,
}

pub fn item_variances(db: &::salsa::Db, path: ItemPath) -> VarianceResultRef<&[Variance]> {
    match path {
        ItemPath::Submodule(_, _) => Ok(&[]),
        ItemPath::MajorItem(path) => match path {
            MajorItemPath::Type(path) => ty_path_variances(db, path).as_ref().map(Vec::as_ref),
            MajorItemPath::Trait(path) => trai_item_variances(db, path).as_ref().map(Vec::as_ref),
            MajorItemPath::Form(_path) => {
                todo!()
                // form_item_variances(db, path).as_ref().map(Vec::as_ref)
            }
        },
        ItemPath::AssocItem(_) => todo!(),
        ItemPath::TypeVariant(_, _) => todo!(),
        ItemPath::ImplBlock(_) => todo!(),
        ItemPath::Attr(_, _) => todo!(),
        ItemPath::Script(_, _) => todo!(),
    }
}

#[salsa::tracked(jar = DecTypeJar, return_ref)]
pub(crate) fn ty_path_variances(db: &::salsa::Db, path: TypePath) -> VarianceResult<Vec<Variance>> {
    calc_item_path_variances(db, path)
}

#[salsa::tracked(jar = DecTypeJar, return_ref)]
pub(crate) fn trai_item_variances(
    db: &::salsa::Db,
    path: TraitPath,
) -> VarianceResult<Vec<Variance>> {
    calc_item_path_variances(db, path)
}

#[salsa::tracked(jar = DecTypeJar, return_ref)]
pub(crate) fn form_path_variances(
    db: &::salsa::Db,
    path: MajorFormPath,
) -> VarianceResult<Vec<Variance>> {
    calc_item_path_variances(db, path)
}

#[salsa::tracked(jar = DecTypeJar, return_ref)]
pub fn ty_item_path_variances(
    db: &::salsa::Db,
    path: TypeItemPath,
) -> VarianceResult<Vec<Variance>> {
    calc_item_path_variances(db, path)
}

fn calc_item_path_variances(
    db: &::salsa::Db,
    path: impl Into<ItemPath>,
) -> VarianceResult<Vec<Variance>> {
    let graph = VarianceGraph::new(db, path.into())?;
    let graph = graph.propagate(1000).unwrap();
    Ok(graph.finish())
}

pub trait HasVariances: Copy {
    fn variances<'a>(self, db: &'a ::salsa::Db) -> VarianceResultRef<'a, &'a [Variance]>;
}

impl HasVariances for TypePath {
    fn variances<'a>(self, db: &'a salsa::Db) -> VarianceResultRef<'a, &'a [Variance]> {
        ty_path_variances(db, self).as_ref().map(|v| v as &[_])
    }
}
