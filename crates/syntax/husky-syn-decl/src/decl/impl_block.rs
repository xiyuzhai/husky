pub mod ill_formed;
pub mod trai_for_ty_impl_block;
pub mod ty_impl_block;

use self::ill_formed::*;
use self::trai_for_ty_impl_block::*;
use self::ty_impl_block::*;
use super::*;
use husky_entity_path::path::impl_block::ImplBlockPath;
use husky_entity_tree::node::impl_block::ImplBlockSynNodePath;
use husky_regional_token::ImplRegionalToken;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum ImplBlockSynNodeDecl {
    Type(TypeImplBlockSynNodeDecl),
    TraitForType(TraitForTypeImplBlockSynNodeDecl),
    IllFormed(IllFormedImplBlockSynNodeDecl),
}

impl ImplBlockSynNodeDecl {
    pub fn syn_node_path(self, db: &::salsa::Db) -> ImplBlockSynNodePath {
        match self {
            ImplBlockSynNodeDecl::Type(decl) => decl.syn_node_path(db).into(),
            ImplBlockSynNodeDecl::TraitForType(decl) => decl.syn_node_path(db).into(),
            ImplBlockSynNodeDecl::IllFormed(decl) => decl.syn_node_path(db).into(),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            ImplBlockSynNodeDecl::Type(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            ImplBlockSynNodeDecl::TraitForType(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            ImplBlockSynNodeDecl::IllFormed(syn_node_decl) => syn_node_decl.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            ImplBlockSynNodeDecl::Type(syn_node_decl) => syn_node_decl.errors(db),
            ImplBlockSynNodeDecl::TraitForType(syn_node_decl) => syn_node_decl.errors(db),
            ImplBlockSynNodeDecl::IllFormed(syn_node_decl) => syn_node_decl.errors(db),
        }
    }
}

impl HasSynNodeDecl for ImplBlockSynNodePath {
    type NodeDecl = ImplBlockSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        match self {
            ImplBlockSynNodePath::TypeImplBlock(syn_node_path) => {
                syn_node_path.syn_node_decl(db).into()
            }
            ImplBlockSynNodePath::TraitForTypeImplBlock(syn_node_path) => {
                syn_node_path.syn_node_decl(db).into()
            }
            ImplBlockSynNodePath::IllFormedImplBlock(syn_node_path) => {
                syn_node_path.syn_node_decl(db).into()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum ImplBlockSynDecl {
    Type(TypeImplBlockSynDecl),
    TraitForType(TraitForTypeImplBlockSynDecl),
}

impl ImplBlockSynDecl {
    pub fn path(self, db: &::salsa::Db) -> ImplBlockPath {
        match self {
            ImplBlockSynDecl::Type(decl) => decl.path(db).into(),
            ImplBlockSynDecl::TraitForType(decl) => decl.path(db).into(),
        }
    }

    pub fn template_parameters<'a>(self, _db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        todo!()
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            ImplBlockSynDecl::Type(decl) => decl.syn_expr_region(db),
            ImplBlockSynDecl::TraitForType(decl) => decl.syn_expr_region(db),
        }
    }
}

impl HasSynDecl for ImplBlockPath {
    type Decl = ImplBlockSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        match self {
            ImplBlockPath::TypeImplBlock(path) => path.syn_decl(db).map(Into::into),
            ImplBlockPath::TraitForTypeImplBlock(path) => path.syn_decl(db).map(Into::into),
        }
    }
}
