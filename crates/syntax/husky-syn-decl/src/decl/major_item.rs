pub mod form;
pub mod trai;
pub mod ty;

use self::form::*;
use self::trai::*;
use self::ty::*;
use super::*;
use husky_entity_path::path::major_item::MajorItemPath;
use husky_entity_tree::node::major_item::MajorItemSynNodePath;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum MajorItemSynNodeDecl {
    Type(TypeSynNodeDecl),
    Form(FormSynNodeDecl),
    Trait(TraitSynNodeDecl),
}

impl MajorItemSynNodeDecl {
    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            MajorItemSynNodeDecl::Type(syn_node_decl) => syn_node_decl.syn_expr_region(db).into(),
            MajorItemSynNodeDecl::Form(syn_node_decl) => syn_node_decl.syn_expr_region(db).into(),
            MajorItemSynNodeDecl::Trait(syn_node_decl) => syn_node_decl.syn_expr_region(db).into(),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            MajorItemSynNodeDecl::Type(syn_node_decl) => syn_node_decl.errors(db),
            MajorItemSynNodeDecl::Form(syn_node_decl) => syn_node_decl.errors(db),
            MajorItemSynNodeDecl::Trait(syn_node_decl) => syn_node_decl.errors(db),
        }
    }
}

impl HasSynNodeDecl for MajorItemSynNodePath {
    type NodeDecl = MajorItemSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        match self {
            MajorItemSynNodePath::Trait(syn_node_path) => syn_node_path.syn_node_decl(db).into(),
            MajorItemSynNodePath::Type(syn_node_path) => syn_node_path.syn_node_decl(db).into(),
            MajorItemSynNodePath::Form(syn_node_path) => syn_node_path.syn_node_decl(db).into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum MajorItemSynDecl {
    Type(TypeSynDecl),
    Trait(TraitSynDecl),
    Form(FormSynDecl),
}

impl MajorItemSynDecl {
    pub fn template_parameters<'a>(self, db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        match self {
            MajorItemSynDecl::Type(decl) => decl.template_parameters(db),
            MajorItemSynDecl::Form(decl) => decl.template_parameters(db),
            MajorItemSynDecl::Trait(decl) => decl.template_parameters(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            MajorItemSynDecl::Type(decl) => decl.syn_expr_region(db),
            MajorItemSynDecl::Form(decl) => decl.syn_expr_region(db),
            MajorItemSynDecl::Trait(decl) => decl.syn_expr_region(db),
        }
    }

    pub fn path(self, db: &::salsa::Db) -> MajorItemPath {
        match self {
            MajorItemSynDecl::Type(decl) => decl.path(db).into(),
            MajorItemSynDecl::Form(decl) => decl.path(db).into(),
            MajorItemSynDecl::Trait(decl) => decl.path(db).into(),
        }
    }
}

impl HasSynDecl for MajorItemPath {
    type Decl = MajorItemSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        match self {
            MajorItemPath::Type(id) => id.syn_decl(db).map(Into::into),
            MajorItemPath::Trait(id) => id.syn_decl(db).map(Into::into),
            MajorItemPath::Form(id) => id.syn_decl(db).map(Into::into),
        }
    }
}
