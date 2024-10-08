mod error;

use crate::{
    collector::EntityTreeCollector,
    node::impl_block::{
        ill_formed_impl_block::ImplBlockIllForm, ty_impl_block::TypeImplBlockSynNodePath,
    },
    *,
};
use husky_entity_path::path::{
    impl_block::{trai_for_ty_impl_block::TraitForTypeImplBlockPath, TypeSketch},
    major_item::{trai::TraitPath, ty::TypePath},
};
use husky_vfs::path::crate_path::CratePath;
use vec_like::VecMap;

#[salsa::tracked(return_ref)]
pub(crate) fn item_tree_crate_bundle(
    db: &::salsa::Db,
    crate_path: CratePath,
) -> EntityTreeCrateBundle {
    EntityTreeCollector::new(db, crate_path).collect_all()
}

#[test]
fn item_tree_crate_bundle_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| item_tree_crate_bundle(db, crate_path),
        &AstTestConfig::new(
            "item_tree_bundle",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    )
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct EntityTreeCrateBundle {
    sheets: VecMap<EntityTreeSheet>,
    principal_item_path_expr_arena: MajorPathExprArena,
}

impl EntityTreeCrateBundle {
    pub(crate) fn new(
        sheets: VecMap<EntityTreeSheet>,
        principal_item_path_expr_arena: MajorPathExprArena,
    ) -> Self {
        Self {
            sheets,
            principal_item_path_expr_arena,
        }
    }

    pub fn sheets(&self) -> &[EntityTreeSheet] {
        &self.sheets
    }

    pub fn all_ty_impl_block_syn_node_paths<'a>(
        &'a self,
    ) -> impl Iterator<Item = TypeImplBlockSynNodePath> + 'a {
        self.sheets
            .iter()
            .map(|sheet| sheet.all_ty_impl_block_syn_node_paths())
            .flatten()
    }

    pub fn all_impl_block_ill_forms<'a>(
        &'a self,
        db: &'a ::salsa::Db,
    ) -> impl Iterator<Item = &'a ImplBlockIllForm> + 'a {
        self.sheets
            .iter()
            .map(|sheet| sheet.all_impl_block_ill_forms(db))
            .flatten()
    }

    pub(crate) fn trai_for_ty_impl_block_paths_filtered_by_trai_path<'a>(
        &'a self,
        db: &'a ::salsa::Db,
        trai_path: TraitPath,
    ) -> impl Iterator<Item = TraitForTypeImplBlockPath> + 'a {
        self.sheets
            .iter()
            .map(|sheet| sheet.all_trai_for_ty_impl_block_paths(db))
            .flatten()
            .filter(move |path| path.trai_path(db) == trai_path)
    }

    pub(crate) fn trai_for_ty_impl_block_paths_filtered_by_ty_path<'a>(
        &'a self,
        db: &'a ::salsa::Db,
        ty_path: TypePath,
    ) -> impl Iterator<Item = TraitForTypeImplBlockPath> + 'a {
        self.sheets
            .iter()
            .flat_map(|sheet| sheet.all_trai_for_ty_impl_block_paths(db))
            .filter(move |path| path.ty_sketch(db) == TypeSketch::Path(ty_path))
    }

    pub(crate) fn get_sheet(&self, module_path: ModulePath) -> Option<&EntityTreeSheet> {
        self.sheets.get_entry(module_path)
    }
}
