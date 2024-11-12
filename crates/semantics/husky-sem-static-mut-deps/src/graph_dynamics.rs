use crate::{builder::SemStaticMutDepsBuilder, static_mut_deps::value::SemValueStaticMutDeps, *};
use ::graph_dynamics::{
    context::{IsGraphDynamicsContext, IsGraphDynamicsScheme},
    cycle_group::CycleGroupMap,
};
use husky_entity_kind::MajorFormKind;
use husky_entity_path::{
    path::{assoc_item::AssocItemPath, major_item::MajorItemPath, ItemPath, ItemPathId},
    region::RegionPath,
};
use husky_eth_signature::signature::attr::AttrEthTemplate;
use husky_eth_term::term::EthTerm;
use husky_sem_item_path_deps::{
    helpers::graph_dynamics::{
        item_sem_item_path_cycle_group_itd, item_sem_item_path_full_deps_cropped,
        SemItemPathDepsCyclceGroupItd, SemItemPathDepsGraphDepsScheme,
    },
    item_path_deps::item_sem_item_path_deps,
};
use husky_term_prelude::ItemPathTerm;
use propagate::{PropagationResult, PropagationResultRef};

pub struct SemStaticMutDepsGraphDynamicsScheme {}

impl IsGraphDynamicsScheme for SemStaticMutDepsGraphDynamicsScheme {
    type Value = SemValueStaticMutDeps;

    const MAX_ITERATION: usize = 1000;
}

#[derive(Clone, Copy)]
pub struct SemStaticMutDepsGraphDynamicsContext<'db> {
    db: &'db ::salsa::Db,
}

impl<'db> IsGraphDynamicsContext<'db> for SemStaticMutDepsGraphDynamicsContext<'db> {
    type DepsScheme = SemItemPathDepsGraphDepsScheme;

    type DynamicsScheme = SemStaticMutDepsGraphDynamicsScheme;

    fn debug_node(self, node: ItemPath) -> String {
        use salsa::DebugWithDb;

        format!("{:?}", node.debug_with(self.db))
    }

    fn deps_cropped(self, node: ItemPath) -> impl IntoIterator<Item = ItemPath> {
        item_sem_item_path_deps(self.db, *node)
            .as_ref()
            .unwrap()
            .iter()
            .copied()
    }

    fn full_deps_cropped(self, node: ItemPath) -> &'db [ItemPath] {
        item_sem_item_path_full_deps_cropped(self.db, *node)
    }

    fn cycle_group_itd(self, node: ItemPath) -> SemItemPathDepsCyclceGroupItd {
        item_sem_item_path_cycle_group_itd(self.db, *node)
    }

    fn initial_value(self, node: ItemPath) -> SemValueStaticMutDeps {
        item_sem_static_mut_deps_initial_value(self.db, *node).clone()
    }

    fn updated_value<'a>(
        self,
        node: ItemPath,
        f: impl Fn(ItemPath) -> &'a SemValueStaticMutDeps,
    ) -> SemValueStaticMutDeps {
        let mut value = f(node).clone();
        let Some(mut builder) =
            SemStaticMutDepsBuilder::new(self.db, RegionPath::ItemDefn(node), f)
        else {
            return value;
        };
        value.merge(&builder.calc_root());
        value
    }

    fn cycle_group_final_values(
        self,
        cycle_group_itd: SemItemPathDepsCyclceGroupItd,
    ) -> PropagationResultRef<'db, &'db CycleGroupMap<Self::DepsScheme, SemValueStaticMutDeps>>
    {
        item_sem_static_mut_deps_cycle_group_final_values(self.db, cycle_group_itd).as_ref()
    }
}

#[salsa::tracked(return_ref)]
fn item_sem_static_mut_deps_initial_value(
    db: &::salsa::Db,
    item_path_id: ItemPathId,
) -> SemValueStaticMutDeps {
    use husky_entity_tree::node::attr::HasAttrPaths;

    let attr_paths = item_path_id.attr_paths(db);
    let mut deps = SemValueStaticMutDeps::default();
    let item_path = item_path_id.item_path(db);
    match item_path {
        ItemPath::Submodule(_, _) => (),
        ItemPath::MajorItem(dep_major_item_path) => match dep_major_item_path {
            MajorItemPath::Type(_) => (),
            MajorItemPath::Trait(_) => (),
            MajorItemPath::Form(dep_major_form_path) => match dep_major_form_path.kind(db) {
                MajorFormKind::Ritchie(_) => (),
                MajorFormKind::TypeAlias => (),
                MajorFormKind::TypeVar => (),
                MajorFormKind::Val => (),
                MajorFormKind::StaticMut => deps.insert(item_path),
                MajorFormKind::StaticVar => (),
                MajorFormKind::Compterm => (),
                MajorFormKind::Conceptual => (),
            },
        },
        ItemPath::AssocItem(assoc_item_path) => match assoc_item_path {
            AssocItemPath::TypeItem(_) => (),         // ad hoc
            AssocItemPath::TraitItem(_) => (),        // ad hoc
            AssocItemPath::TraitForTypeItem(_) => (), // ad hoc
        },
        ItemPath::TypeVariant(_, _) => (),
        ItemPath::ImplBlock(_) => (),
        ItemPath::Attr(_, _) => (),
        ItemPath::Script(_, _) => (),
    };
    for attr_path in attr_paths {
        use husky_eth_signature::signature::HasEthTemplate;

        let AttrEthTemplate::Dep(deps_eth_template) = attr_path.eth_template(db).unwrap() else {
            continue;
        };
        for shard in deps_eth_template.shards(db) {
            match shard.dep_term(db) {
                EthTerm::Literal(_) => todo!(),
                EthTerm::SymbolicVariable(_) => todo!(),
                EthTerm::AbstractVariable(_) => todo!(),
                EthTerm::ItemPath(path) => match path {
                    ItemPathTerm::MajorForm(path) => match path.kind(db) {
                        MajorFormKind::Ritchie(_) => (),
                        MajorFormKind::TypeAlias => (),
                        MajorFormKind::TypeVar => (),
                        MajorFormKind::Val => (),
                        MajorFormKind::StaticMut => todo!(),
                        MajorFormKind::StaticVar => (),
                        MajorFormKind::Compterm => (),
                        MajorFormKind::Conceptual => (),
                    },
                    ItemPathTerm::Trait(_) => todo!(),
                    ItemPathTerm::TypeOntology(_) => todo!(),
                    ItemPathTerm::TypeInstance(_) => todo!(),
                    ItemPathTerm::TypeVariant(_) => todo!(),
                },
                EthTerm::Sort(_) => todo!(),
                EthTerm::Universe(_) => todo!(),
                EthTerm::Curry(_) => todo!(),
                EthTerm::Ritchie(_) => todo!(),
                EthTerm::Abstraction(_) => todo!(),
                EthTerm::Application(_) => todo!(),
                EthTerm::TypeAsTraitItem(_) => todo!(),
                EthTerm::TraitConstraint(_) => todo!(),
            }
        }
    }
    deps
}

#[salsa::tracked(return_ref)]
fn item_sem_static_mut_deps_cycle_group_final_values(
    db: &::salsa::Db,
    cycle_group_itd: SemItemPathDepsCyclceGroupItd,
) -> PropagationResult<CycleGroupMap<SemItemPathDepsGraphDepsScheme, SemValueStaticMutDeps>> {
    let ctx = SemStaticMutDepsGraphDynamicsContext { db };
    let cycle_group = cycle_group_itd.cycle_group(db);
    ctx.calc_cycle_group_final_values(cycle_group)
}

pub fn item_sem_static_mut_deps<'db>(
    db: &'db ::salsa::Db,
    item_path: ItemPath,
) -> &'db SemValueStaticMutDeps {
    let ctx = SemStaticMutDepsGraphDynamicsContext { db };
    ctx.final_value(item_path).unwrap()
}

#[test]
fn item_sem_static_mut_deps_works() {
    DB::ast_rich_test_debug_with_db(
        item_sem_static_mut_deps,
        &AstTestConfig::new(
            "item_sem_static_mut_deps",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SEMANTICS,
        ),
    );
}
