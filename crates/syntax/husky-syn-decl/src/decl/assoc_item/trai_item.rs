pub mod assoc_ritchie;
pub mod assoc_static_mut;
pub mod assoc_static_var;
pub mod assoc_ty;
pub mod assoc_val;
pub mod memo;
pub mod method_ritchie;

use self::{
    assoc_ritchie::*,
    assoc_static_mut::{TraitAssocStaticMutSynDecl, TraitAssocStaticMutSynNodeDecl},
    assoc_static_var::{TraitAssocStaticVarSynDecl, TraitAssocStaticVarSynNodeDecl},
    assoc_ty::*,
    assoc_val::*,
    memo::TraitMemoizedFieldSynNodeDecl,
    method_ritchie::*,
};
use super::*;
use husky_entity_kind::TraitItemKind;
use husky_entity_path::path::assoc_item::trai_item::TraitItemPath;
use husky_entity_tree::node::assoc_item::trai_item::TraitItemSynNodePath;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TraitItemSynNodeDecl {
    AssocRitchie(TraitAssocRitchieSynNodeDecl),
    MethodRitchie(TraitMethodRitchieSynNodeDecl),
    MemoizedField(TraitMemoizedFieldSynNodeDecl),
    AssocStaticMut(TraitAssocStaticMutSynNodeDecl),
    AssocStaticVar(TraitAssocStaticVarSynNodeDecl),
    AssocType(TraitAssocTypeSynNodeDecl),
    AssocVal(TraitAssocValSynNodeDecl),
}

impl TraitItemSynNodeDecl {
    pub fn syn_node_path(self, db: &::salsa::Db) -> TraitItemSynNodePath {
        match self {
            TraitItemSynNodeDecl::AssocRitchie(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::MethodRitchie(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::MemoizedField(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::AssocType(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::AssocStaticMut(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::AssocStaticVar(slf) => slf.syn_node_path(db),
            TraitItemSynNodeDecl::AssocVal(slf) => slf.syn_node_path(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TraitItemSynNodeDecl::AssocRitchie(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::MethodRitchie(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::MemoizedField(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::AssocType(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::AssocStaticMut(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::AssocStaticVar(slf) => slf.syn_expr_region(db),
            TraitItemSynNodeDecl::AssocVal(slf) => slf.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            TraitItemSynNodeDecl::AssocRitchie(slf) => slf.errors(db),
            TraitItemSynNodeDecl::MethodRitchie(slf) => slf.errors(db),
            TraitItemSynNodeDecl::MemoizedField(slf) => slf.errors(db),
            TraitItemSynNodeDecl::AssocType(slf) => slf.errors(db),
            TraitItemSynNodeDecl::AssocStaticMut(slf) => slf.errors(db),
            TraitItemSynNodeDecl::AssocStaticVar(slf) => slf.errors(db),
            TraitItemSynNodeDecl::AssocVal(slf) => slf.errors(db),
        }
    }
}

impl HasSynNodeDecl for TraitItemSynNodePath {
    type NodeDecl = TraitItemSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        trai_item_syn_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
fn trai_item_syn_node_decl(
    db: &::salsa::Db,
    syn_node_path: TraitItemSynNodePath,
) -> TraitItemSynNodeDecl {
    let parser = ItemSynNodeDeclParser::new(db, syn_node_path.into());
    parser.parse_trai_item_syn_node_decl(syn_node_path)
}

impl<'a> ItemSynNodeDeclParser<'a> {
    fn parse_trai_item_syn_node_decl(
        &self,
        syn_node_path: TraitItemSynNodePath,
    ) -> TraitItemSynNodeDecl {
        match syn_node_path.item_kind(self.db()) {
            TraitItemKind::MemoizedField => {
                self.parse_trai_memo_syn_node_decl(syn_node_path).into()
            }
            TraitItemKind::MethodRitchie(_) => self
                .parse_trai_method_ritchie_syn_node_decl(syn_node_path)
                .into(),
            TraitItemKind::AssocType => self.parse_trai_assoc_ty_node_decl(syn_node_path).into(),
            TraitItemKind::AssocVal => self.parse_trai_assoc_val_node_decl(syn_node_path).into(),
            TraitItemKind::AssocRitchie(_) => self
                .parse_trai_assoc_ritchie_node_decl(syn_node_path)
                .into(),
            TraitItemKind::AssocConceptual => todo!(),
            TraitItemKind::AssocStaticMut => self
                .parse_trai_assoc_static_mut_node_decl(syn_node_path)
                .into(),
            TraitItemKind::AssocStaticVar => self
                .parse_trai_assoc_static_var_node_decl(syn_node_path)
                .into(),
            TraitItemKind::AssocCompterm => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TraitItemSynDecl {
    AssocRitchie(TraitAssocRitchieSynDecl),
    MethodFn(TraitMethodRitchieSynDecl),
    AssocType(TraitAssocTypeSynDecl),
    AssocStaticMut(TraitAssocStaticMutSynDecl),
    AssocStaticVar(TraitAssocStaticVarSynDecl),
    AssocVal(TraitAssocValSynDecl),
}

/// # constructor
impl TraitItemSynDecl {
    fn from_node(
        db: &::salsa::Db,
        path: TraitItemPath,
        syn_node_decl: TraitItemSynNodeDecl,
    ) -> SynDeclResult<Self> {
        Ok(match syn_node_decl {
            TraitItemSynNodeDecl::AssocRitchie(syn_node_decl) => {
                TraitAssocRitchieSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TraitItemSynNodeDecl::MethodRitchie(syn_node_decl) => {
                TraitMethodRitchieSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TraitItemSynNodeDecl::MemoizedField(_) => todo!(),
            TraitItemSynNodeDecl::AssocType(syn_node_decl) => {
                TraitAssocTypeSynDecl::from_node(path, syn_node_decl, db)?.into()
            }
            TraitItemSynNodeDecl::AssocVal(_) => todo!(),
            TraitItemSynNodeDecl::AssocStaticMut(_) => todo!(),
            TraitItemSynNodeDecl::AssocStaticVar(syn_node_decl) => {
                TraitAssocStaticVarSynDecl::from_node(path, syn_node_decl, db)?.into()
            }
        })
    }
}

/// # getters
impl TraitItemSynDecl {
    pub fn path(self, db: &::salsa::Db) -> TraitItemPath {
        match self {
            TraitItemSynDecl::AssocRitchie(slf) => slf.path(db),
            TraitItemSynDecl::MethodFn(slf) => slf.path(db),
            TraitItemSynDecl::AssocType(slf) => slf.path(db),
            TraitItemSynDecl::AssocStaticMut(slf) => slf.path(db),
            TraitItemSynDecl::AssocStaticVar(slf) => slf.path(db),
            TraitItemSynDecl::AssocVal(slf) => slf.path(db),
        }
    }

    pub fn template_parameters<'a>(self, db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        match self {
            TraitItemSynDecl::AssocRitchie(slf) => slf.template_parameters(db),
            TraitItemSynDecl::MethodFn(slf) => slf.template_parameters(db),
            TraitItemSynDecl::AssocType(slf) => slf.template_parameters(db),
            TraitItemSynDecl::AssocStaticMut(_slf) => &[],
            TraitItemSynDecl::AssocStaticVar(_slf) => &[],
            TraitItemSynDecl::AssocVal(_slf) => &[],
        }
    }

    pub fn parenate_parameters<'a>(
        self,
        db: &'a ::salsa::Db,
    ) -> Option<&'a [ParenateParameterSyndicate]> {
        match self {
            TraitItemSynDecl::AssocRitchie(syn_decl) => Some(syn_decl.parenate_parameters(db)),
            TraitItemSynDecl::MethodFn(syn_decl) => Some(syn_decl.parenate_parameters(db)),
            TraitItemSynDecl::AssocType(_) => None,
            TraitItemSynDecl::AssocVal(_) => None,
            TraitItemSynDecl::AssocStaticMut(_) => None,
            TraitItemSynDecl::AssocStaticVar(_) => None,
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TraitItemSynDecl::AssocRitchie(slf) => slf.syn_expr_region(db),
            TraitItemSynDecl::MethodFn(slf) => slf.syn_expr_region(db),
            TraitItemSynDecl::AssocType(slf) => slf.syn_expr_region(db),
            TraitItemSynDecl::AssocVal(slf) => slf.syn_expr_region(db),
            TraitItemSynDecl::AssocStaticMut(slf) => slf.syn_expr_region(db),
            TraitItemSynDecl::AssocStaticVar(slf) => slf.syn_expr_region(db),
        }
    }
}

impl HasSynDecl for TraitItemPath {
    type Decl = TraitItemSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        trai_item_syn_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn trai_item_syn_decl(
    db: &::salsa::Db,
    path: TraitItemPath,
) -> SynDeclResult<TraitItemSynDecl> {
    let syn_node_decl = path.syn_node_path(db).syn_node_decl(db);
    TraitItemSynDecl::from_node(db, path, syn_node_decl)
}
