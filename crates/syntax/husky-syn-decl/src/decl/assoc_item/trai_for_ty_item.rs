pub mod assoc_compterm;
pub mod assoc_ritchie;
pub mod assoc_static_mut;
pub mod assoc_static_var;
pub mod assoc_ty;
pub mod assoc_val;
pub mod memo;
pub mod method_ritchie;

use self::{assoc_ritchie::*, assoc_static_mut::*, assoc_ty::*, assoc_val::*, method_ritchie::*};
use super::*;
use husky_entity_kind::TraitItemKind;
use husky_entity_path::path::assoc_item::trai_for_ty_item::TraitForTypeItemPath;
use husky_entity_tree::node::assoc_item::trai_for_ty_item::TraitForTypeItemSynNodePath;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TraitForTypeItemSynNodeDecl {
    AssocRitchie(TraitForTypeAssocRitchieSynNodeDecl),
    MethodFn(TraitForTypeMethodRitchieSynNodeDecl),
    AssocType(TraitForTypeAssocTypeSynNodeDecl),
    AssocVal(TraitForTypeAssocValSynNodeDecl),
}

impl From<TraitForTypeItemSynNodeDecl> for ItemSynNodeDecl {
    fn from(decl: TraitForTypeItemSynNodeDecl) -> Self {
        ItemSynNodeDecl::AssocItem(decl.into())
    }
}

impl TraitForTypeItemSynNodeDecl {
    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TraitForTypeItemSynNodeDecl::AssocRitchie(slf) => slf.syn_expr_region(db),
            TraitForTypeItemSynNodeDecl::MethodFn(slf) => slf.syn_expr_region(db),
            TraitForTypeItemSynNodeDecl::AssocType(slf) => slf.syn_expr_region(db),
            TraitForTypeItemSynNodeDecl::AssocVal(slf) => slf.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            TraitForTypeItemSynNodeDecl::AssocRitchie(slf) => slf.errors(db),
            TraitForTypeItemSynNodeDecl::MethodFn(slf) => slf.errors(db),
            TraitForTypeItemSynNodeDecl::AssocType(slf) => slf.errors(db),
            TraitForTypeItemSynNodeDecl::AssocVal(slf) => slf.errors(db),
        }
    }
}

impl HasSynNodeDecl for TraitForTypeItemSynNodePath {
    type NodeDecl = TraitForTypeItemSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        trai_for_ty_item_syn_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn trai_for_ty_item_syn_node_decl(
    db: &::salsa::Db,
    syn_node_path: TraitForTypeItemSynNodePath,
) -> TraitForTypeItemSynNodeDecl {
    let parser = ItemSynNodeDeclParser::new(db, syn_node_path.into());
    parser.parse_trai_for_ty_item_syn_node_decl()
}

impl<'a> ItemSynNodeDeclParser<'a> {
    fn parse_trai_for_ty_item_syn_node_decl(&self) -> TraitForTypeItemSynNodeDecl {
        let db = self.db();
        let ItemSynNodePath::AssocItem(AssocItemSynNodePath::TraitForTypeItem(syn_node_path)) =
            self.syn_node_path()
        else {
            unreachable!()
        };
        match syn_node_path.data(db).item_kind(db) {
            TraitItemKind::MemoizedField => todo!(),
            TraitItemKind::MethodRitchie(ritchie_item_kind) => self
                .parse_trai_for_ty_method_ritchie_node_decl(syn_node_path, ritchie_item_kind)
                .into(),
            TraitItemKind::AssocType => self
                .parse_trai_for_ty_assoc_ty_node_decl(syn_node_path)
                .into(),
            TraitItemKind::AssocVal => todo!(),
            TraitItemKind::AssocRitchie(ritchie_item_kind) => self
                .parse_trai_for_ty_assoc_ritchie_node_decl(syn_node_path, ritchie_item_kind)
                .into(),
            TraitItemKind::AssocConceptual => todo!(),
            TraitItemKind::AssocStaticMut => todo!(),
            TraitItemKind::AssocStaticVar => todo!(),
            TraitItemKind::AssocCompterm => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TraitForTypeItemSynDecl {
    AssocRitchie(TraitForTypeAssocRitchieSynDecl),
    MethodFn(TraitForTypeMethodRitchieSynDecl),
    AssocType(TraitForTypeAssocTypeSynDecl),
    AssocVal(TraitForTypeAssocValSynDecl),
}

impl From<TraitForTypeItemSynDecl> for SynDecl {
    fn from(decl: TraitForTypeItemSynDecl) -> Self {
        SynDecl::AssocItem(decl.into())
    }
}

/// # constructor
impl TraitForTypeItemSynDecl {
    fn from_node(
        db: &::salsa::Db,
        path: TraitForTypeItemPath,
        syn_node_decl: TraitForTypeItemSynNodeDecl,
    ) -> SynDeclResult<Self> {
        Ok(match syn_node_decl {
            TraitForTypeItemSynNodeDecl::AssocRitchie(syn_node_decl) => {
                TraitForTypeAssocRitchieSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TraitForTypeItemSynNodeDecl::MethodFn(syn_node_decl) => {
                TraitForTypeMethodRitchieSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TraitForTypeItemSynNodeDecl::AssocType(syn_node_decl) => {
                TraitForTypeAssocTypeSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TraitForTypeItemSynNodeDecl::AssocVal(_) => todo!(),
        })
    }
}

/// # getters
impl TraitForTypeItemSynDecl {
    pub fn path(self, db: &::salsa::Db) -> TraitForTypeItemPath {
        match self {
            TraitForTypeItemSynDecl::AssocRitchie(decl) => decl.path(db),
            TraitForTypeItemSynDecl::MethodFn(decl) => decl.path(db),
            TraitForTypeItemSynDecl::AssocType(decl) => decl.path(db),
            TraitForTypeItemSynDecl::AssocVal(decl) => decl.path(db),
        }
    }

    pub fn template_parameters<'a>(self, db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        match self {
            TraitForTypeItemSynDecl::AssocRitchie(decl) => decl.template_parameters(db),
            TraitForTypeItemSynDecl::MethodFn(decl) => decl.template_parameters(db),
            TraitForTypeItemSynDecl::AssocType(decl) => decl.template_parameters(db),
            TraitForTypeItemSynDecl::AssocVal(_) => &[],
        }
    }

    pub fn parenate_parameters<'a>(
        self,
        db: &'a ::salsa::Db,
    ) -> Option<&'a [ParenateParameterSyndicate]> {
        match self {
            TraitForTypeItemSynDecl::AssocRitchie(syn_decl) => {
                Some(syn_decl.parenate_parameters(db))
            }
            TraitForTypeItemSynDecl::MethodFn(syn_decl) => Some(syn_decl.parenate_parameters(db)),
            TraitForTypeItemSynDecl::AssocType(_) => None,
            TraitForTypeItemSynDecl::AssocVal(_) => None,
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TraitForTypeItemSynDecl::AssocRitchie(decl) => decl.syn_expr_region(db),
            TraitForTypeItemSynDecl::MethodFn(decl) => decl.syn_expr_region(db),
            TraitForTypeItemSynDecl::AssocType(decl) => decl.syn_expr_region(db),
            TraitForTypeItemSynDecl::AssocVal(decl) => decl.syn_expr_region(db),
        }
    }
}

impl HasSynDecl for TraitForTypeItemPath {
    type Decl = TraitForTypeItemSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        trai_for_ty_item_syn_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn trai_for_ty_item_syn_decl(
    db: &::salsa::Db,
    path: TraitForTypeItemPath,
) -> SynDeclResult<TraitForTypeItemSynDecl> {
    let syn_node_decl = path.syn_node_path(db).syn_node_decl(db);
    TraitForTypeItemSynDecl::from_node(db, path, syn_node_decl)
}
