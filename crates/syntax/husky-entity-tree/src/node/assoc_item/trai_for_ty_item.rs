use super::*;
use crate::node::impl_block::trai_for_ty_impl_block::TraitForTypeImplBlockSynNodePath;
use husky_entity_path::path::{
    assoc_item::trai_for_ty_item::TraitForTypeItemPath, impl_block::TypeSketch,
    major_item::trai::TraitPath,
};

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[salsa::as_id]
#[salsa::deref_id]
pub struct TraitForTypeItemSynNodePath(ItemSynNodePathId);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraitForTypeItemSynNodePathData {
    disambiguated_item_path: DisambiguatedItemPath<TraitForTypeItemPath>,
}

impl From<TraitForTypeItemSynNodePath> for ItemSynNodePath {
    fn from(path: TraitForTypeItemSynNodePath) -> Self {
        ItemSynNodePath::AssocItem(path.into())
    }
}

impl TraitForTypeItemSynNodePath {
    fn new(
        db: &::salsa::Db,
        registry: &mut ItemSynNodePathRegistry,
        path: TraitForTypeItemPath,
    ) -> Self {
        Self(ItemSynNodePathId::new(
            db,
            ItemSynNodePathData::AssocItem(AssocItemSynNodePathData::TraitForTypeItem(
                TraitForTypeItemSynNodePathData {
                    disambiguated_item_path: registry.issue_maybe_ambiguous_path(path),
                },
            )),
        ))
    }

    pub fn data(self, db: &::salsa::Db) -> TraitForTypeItemSynNodePathData {
        match self.0.data(db) {
            ItemSynNodePathData::AssocItem(AssocItemSynNodePathData::TraitForTypeItem(data)) => {
                data
            }
            _ => unreachable!(),
        }
    }

    pub fn path(self, db: &::salsa::Db) -> Option<TraitForTypeItemPath> {
        Some(match self.0.unambiguous_item_path(db)? {
            ItemPath::AssocItem(AssocItemPath::TraitForTypeItem(path)) => path,
            _ => unreachable!(),
        })
    }

    pub fn ident(self, db: &::salsa::Db) -> Ident {
        self.data(db)
            .disambiguated_item_path
            .maybe_ambiguous_item_path
            .ident(db)
    }

    pub fn trai_path(self, db: &::salsa::Db) -> TraitPath {
        self.data(db)
            .disambiguated_item_path
            .maybe_ambiguous_item_path
            .impl_block(db)
            .trai_path(db)
    }

    pub fn ty_sketch(self, db: &::salsa::Db) -> TypeSketch {
        self.data(db)
            .disambiguated_item_path
            .maybe_ambiguous_item_path
            .impl_block(db)
            .ty_sketch(db)
    }
}

impl TraitForTypeItemSynNodePathData {
    #[inline(always)]
    pub fn syn_node_path(self, id: ItemSynNodePathId) -> TraitForTypeItemSynNodePath {
        TraitForTypeItemSynNodePath(id)
    }

    pub fn path(&self) -> Option<TraitForTypeItemPath> {
        self.disambiguated_item_path.unambiguous_item_path()
    }

    pub fn module_path(self, db: &::salsa::Db) -> ModulePath {
        self.disambiguated_item_path
            .maybe_ambiguous_item_path
            .module_path(db)
    }

    pub fn impl_block(&self, db: &::salsa::Db) -> TraitForTypeImplBlockSynNodePath {
        self.disambiguated_item_path
            .maybe_ambiguous_item_path
            .impl_block(db)
            .syn_node_path(db)
    }

    pub fn item_kind(&self, db: &::salsa::Db) -> TraitItemKind {
        self.disambiguated_item_path
            .maybe_ambiguous_item_path
            .item_kind(db)
    }

    pub fn ast_idx(self, id: ItemSynNodePathId, db: &::salsa::Db) -> AstIdx {
        self.syn_node(TraitForTypeItemSynNodePath(id), db).ast_idx
    }

    pub(crate) fn syn_node<'a>(
        &'a self,
        syn_node_path: TraitForTypeItemSynNodePath,
        db: &'a ::salsa::Db,
    ) -> &'a TraitForTypeItemSynNode {
        self.impl_block(db)
            .assoc_items(db)
            .iter()
            .find_map(|&(_, node_path1, ref node)| (node_path1 == syn_node_path).then_some(node))
            .expect("some")
    }
}

impl HasSynNodePath for TraitForTypeItemPath {
    type SynNodePath = TraitForTypeItemSynNodePath;

    fn syn_node_path(self, db: &::salsa::Db) -> Self::SynNodePath {
        TraitForTypeItemSynNodePath(ItemSynNodePathId::new(
            db,
            ItemSynNodePathData::AssocItem(AssocItemSynNodePathData::TraitForTypeItem(
                TraitForTypeItemSynNodePathData {
                    disambiguated_item_path: DisambiguatedItemPath::from_path(self),
                },
            )),
        ))
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct TraitForTypeItemSynNode {
    syn_node_path: TraitForTypeItemSynNodePath,
    ast_idx: AstIdx,
    ident: Ident,
    item_kind: TraitItemKind,
    visibility: Scope,
    is_generic: bool,
}

/// # constructor
impl TraitForTypeItemSynNode {
    #[inline(always)]
    pub(crate) fn new(
        db: &::salsa::Db,
        registry: &mut ItemSynNodePathRegistry,
        impl_block_syn_node_path: TraitForTypeImplBlockSynNodePath,
        ast_idx: AstIdx,
        ident: Ident,
        item_kind: TraitItemKind,
        visibility: Scope,
        is_generic: bool,
    ) -> (TraitForTypeItemSynNodePath, Self) {
        let path =
            TraitForTypeItemPath::new(impl_block_syn_node_path.path(db), ident, item_kind, db);
        let syn_node_path = TraitForTypeItemSynNodePath::new(db, registry, path);
        (
            syn_node_path,
            Self {
                syn_node_path,
                ast_idx,
                ident,
                item_kind,
                visibility,
                is_generic,
            },
        )
    }
}
