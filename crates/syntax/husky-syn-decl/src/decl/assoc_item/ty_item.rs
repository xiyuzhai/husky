pub mod assoc_ritchie;
pub mod assoc_ty;
pub mod assoc_val;
pub mod memo;
pub mod method_ritchie;

use self::assoc_ritchie::*;
use self::assoc_ty::*;
use self::assoc_val::*;
use self::memo::*;
use self::method_ritchie::*;
use super::*;
use husky_entity_kind::TypeItemKind;
use husky_entity_path::path::assoc_item::ty_item::TypeItemPath;
use husky_entity_tree::node::assoc_item::ty_item::TypeItemSynNodePath;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeItemSynNodeDecl {
    AssocRitchie(TypeAssocRitchieSynNodeDecl),
    MethodFn(TypeMethodRitchieSynNodeDecl),
    AssocType(TypeAssocTypeSynNodeDecl),
    AssocVal(TypeAssocValSynNodeDecl),
    MemoizedField(TypeMemoizedFieldSynNodeDecl),
}

impl From<TypeItemSynNodeDecl> for ItemSynNodeDecl {
    fn from(decl: TypeItemSynNodeDecl) -> Self {
        ItemSynNodeDecl::AssocItem(decl.into())
    }
}

impl TypeItemSynNodeDecl {
    pub fn syn_node_path(self, db: &::salsa::Db) -> TypeItemSynNodePath {
        match self {
            TypeItemSynNodeDecl::AssocRitchie(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeItemSynNodeDecl::MethodFn(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeItemSynNodeDecl::AssocType(_) => todo!(),
            TypeItemSynNodeDecl::AssocVal(_) => todo!(),
            TypeItemSynNodeDecl::MemoizedField(syn_node_decl) => syn_node_decl.syn_node_path(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeItemSynNodeDecl::AssocRitchie(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeItemSynNodeDecl::MethodFn(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeItemSynNodeDecl::AssocType(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeItemSynNodeDecl::AssocVal(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeItemSynNodeDecl::MemoizedField(syn_node_decl) => syn_node_decl.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            TypeItemSynNodeDecl::AssocRitchie(syn_node_decl) => syn_node_decl.errors(db),
            TypeItemSynNodeDecl::MethodFn(syn_node_decl) => syn_node_decl.errors(db),
            TypeItemSynNodeDecl::AssocType(syn_node_decl) => syn_node_decl.errors(db),
            TypeItemSynNodeDecl::AssocVal(syn_node_decl) => syn_node_decl.errors(db),
            TypeItemSynNodeDecl::MemoizedField(syn_node_decl) => syn_node_decl.errors(db),
        }
    }
}

impl HasSynNodeDecl for TypeItemSynNodePath {
    type NodeDecl = TypeItemSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        ty_item_syn_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_item_syn_node_decl(
    db: &::salsa::Db,
    syn_node_path: TypeItemSynNodePath,
) -> TypeItemSynNodeDecl {
    let ctx = ItemSynNodeDeclParser::new(db, syn_node_path.into());
    ctx.parse_ty_item_syn_node_decl(syn_node_path)
}

impl<'a> ItemSynNodeDeclParser<'a> {
    fn parse_ty_item_syn_node_decl(
        &self,
        syn_node_path: TypeItemSynNodePath,
    ) -> TypeItemSynNodeDecl {
        let db = self.db();
        match syn_node_path.data(db).item_kind(self.db()) {
            TypeItemKind::AssocRitchie(_) => self.parse_ty_assoc_fn_node_decl(syn_node_path).into(),
            TypeItemKind::MethodRitchie(_) => self.parse_ty_method_node_decl(syn_node_path).into(),
            TypeItemKind::MemoizedField => self.parse_ty_memo_syn_node_decl(syn_node_path).into(),
            TypeItemKind::AssocVal => todo!(),
            TypeItemKind::AssocType => todo!(),
            TypeItemKind::AssocConceptual => todo!(),
            TypeItemKind::AssocStaticMut => todo!(),
            TypeItemKind::AssocStaticVar => todo!(),
            TypeItemKind::AssocCompterm => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeItemSynDecl {
    AssocRitchie(TypeAssocRitchieSynDecl),
    MethodFn(TypeMethodRitchieSynDecl),
    // MethodFunction(TypeMethodCurrySynDecl),
    AssocType(TypeAssocTypeSynDecl),
    AssocVal(TypeAssocValSynDecl),
    MemoizedField(TypeMemoizedFieldSynDecl),
}

impl From<TypeItemSynDecl> for SynDecl {
    fn from(decl: TypeItemSynDecl) -> Self {
        SynDecl::AssocItem(decl.into())
    }
}

impl TypeItemSynDecl {
    pub fn path(self, db: &::salsa::Db) -> TypeItemPath {
        match self {
            TypeItemSynDecl::AssocRitchie(slf) => slf.path(db),
            TypeItemSynDecl::MethodFn(slf) => slf.path(db),
            TypeItemSynDecl::AssocType(slf) => slf.path(db),
            TypeItemSynDecl::AssocVal(slf) => slf.path(db),
            TypeItemSynDecl::MemoizedField(slf) => slf.path(db),
        }
    }

    pub fn template_parameters<'a>(self, db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        match self {
            TypeItemSynDecl::AssocRitchie(slf) => slf.template_parameters(db),
            TypeItemSynDecl::MethodFn(slf) => slf.template_parameters(db),
            // TypeItemSynDecl::MethodFunction(decl) => todo!(),
            TypeItemSynDecl::AssocType(slf) => slf.template_parameters(db),
            TypeItemSynDecl::AssocVal(_slf) => &[],
            TypeItemSynDecl::MemoizedField(_slf) => &[],
        }
    }

    pub fn parenate_parameters<'a>(
        self,
        db: &'a ::salsa::Db,
    ) -> Option<&'a [ParenateParameterSyndicate]> {
        match self {
            TypeItemSynDecl::AssocRitchie(syn_decl) => Some(syn_decl.parenate_parameters(db)),
            TypeItemSynDecl::MethodFn(syn_decl) => Some(syn_decl.parenate_parameters(db)),
            TypeItemSynDecl::AssocType(_) => None,
            TypeItemSynDecl::AssocVal(_) => None,
            TypeItemSynDecl::MemoizedField(_) => None,
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeItemSynDecl::AssocRitchie(decl) => decl.syn_expr_region(db),
            TypeItemSynDecl::MethodFn(decl) => decl.syn_expr_region(db),
            // TypeItemSynDecl::MethodFunction(decl) => decl.syn_expr_region(db),
            TypeItemSynDecl::AssocType(decl) => decl.syn_expr_region(db),
            TypeItemSynDecl::AssocVal(decl) => decl.syn_expr_region(db),
            TypeItemSynDecl::MemoizedField(decl) => decl.syn_expr_region(db),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeItemDecls {
    AssocRitchie(SmallVecImpl<TypeAssocRitchieSynDecl>),
    MethodFn(SmallVecImpl<TypeMethodRitchieSynDecl>),
    MethodFunction(/* adhoc */),
    AssocType(SmallVecImpl<TypeAssocTypeSynDecl>),
    AssocVal(SmallVecImpl<TypeAssocValSynDecl>),
    MemoizedField(SmallVecImpl<TypeMemoizedFieldSynDecl>),
}

impl HasSynDecl for TypeItemPath {
    type Decl = TypeItemSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        ty_item_syn_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_item_syn_decl(
    db: &::salsa::Db,
    path: TypeItemPath,
) -> SynDeclResult<TypeItemSynDecl> {
    match path.syn_node_path(db).syn_node_decl(db) {
        TypeItemSynNodeDecl::AssocRitchie(syn_node_decl) => {
            TypeAssocRitchieSynDecl::from_node(db, path, syn_node_decl).map(Into::into)
        }
        TypeItemSynNodeDecl::MethodFn(syn_node_decl) => {
            TypeMethodRitchieSynDecl::from_node(db, path, syn_node_decl).map(Into::into)
        }
        TypeItemSynNodeDecl::AssocType(_) => todo!(),
        TypeItemSynNodeDecl::AssocVal(syn_node_decl) => {
            TypeAssocValSynDecl::from_node(db, path, syn_node_decl).map(Into::into)
        }
        TypeItemSynNodeDecl::MemoizedField(syn_node_decl) => {
            TypeMemoizedFieldSynDecl::from_node(db, path, syn_node_decl).map(Into::into)
        }
    }
}
