pub mod db;

use self::db::DevComptimeDb;

use husky_devsoul::devsoul::IsDevsoul;
use husky_entity_kind::{MajorFormKind, TraitItemKind, TypeItemKind};
use husky_entity_path::path::{assoc_item::AssocItemPath, major_item::MajorItemPath, ItemPath};
use husky_ki::Ki;
use husky_ki_repr::{
    repr::{KiCachingClass, KiRepr},
    var_deps::KiVarDeps,
};
use husky_linket::linket::Linket;
use husky_linket_impl::dev_eval_context::IsDevRuntimeInterfaceDyn;
use husky_linktime::IsLinktime;
use husky_manifest::helpers::upstream::HasAllUpstreamPackages;
use husky_toolchain_config::toolchain_config;
use husky_vfs::{
    error::VfsResult,
    path::{
        crate_path::{CrateKind, CratePath},
        linktime_target_path::LinktimeTargetPath,
        package_path::PackagePath,
    },
};
use std::path::Path;

pub struct DevComptime<Devsoul: IsDevsoul> {
    db: DevComptimeDb,
    target: DevComptimeTarget,
    target_path: Option<LinktimeTargetPath>,
    linktime: Devsoul::Linktime,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DevComptimeTarget {
    None,
    SingleCrate(CratePath),
}

impl<Devsoul: IsDevsoul> DevComptime<Devsoul> {
    pub fn new(target_crate_path: impl AsRef<Path>) -> VfsResult<Self> {
        let target_crate_path = target_crate_path.as_ref();
        let db = DevComptimeDb::default();
        let toolchain = toolchain_config(target_crate_path, &*db).toolchain();
        let target_package_path =
            match PackagePath::new_local_or_toolchain_package(&db, toolchain, target_crate_path) {
                Ok(package_path) => package_path,
                Err(e) => todo!(
                    "Handle error creating PackagePath for `{}`: {}",
                    target_crate_path.display(),
                    e
                ),
            };
        let Some(target_crate_path) =
            CratePath::new(target_package_path, CrateKind::Main, &db).into_result_option()?
        else {
            todo!()
        };
        let target = DevComptimeTarget::SingleCrate(target_crate_path);
        let target_path = match target {
            DevComptimeTarget::None => None,
            DevComptimeTarget::SingleCrate(crate_path) => Some(LinktimeTargetPath::new_package(
                crate_path.package_path(&db),
                &db,
            )),
        };
        Ok(Self {
            linktime: IsLinktime::new(
                /* ad hoc */
                LinktimeTargetPath::new_package(target_crate_path.package_path(&db), &db),
                &db,
            ),
            target,
            target_path,
            db,
        })
    }

    pub fn init(&self, runtime: &'static dyn IsDevRuntimeInterfaceDyn<Devsoul::LinketImpl>) {
        self.linktime.init(runtime)
    }

    pub fn linktime(&self) -> &Devsoul::Linktime {
        &self.linktime
    }
}

impl<Devsoul: IsDevsoul> DevComptime<Devsoul> {
    pub fn target(&self) -> DevComptimeTarget {
        self.target
    }

    pub fn linktime_target_path(&self) -> Option<LinktimeTargetPath> {
        self.target_path
    }

    pub fn linket_impl(&self, linket: Linket) -> Devsoul::LinketImpl {
        self.linktime.linket_impl(linket, self.db())
    }
}

impl<Devsoul: IsDevsoul> DevComptime<Devsoul> {
    pub fn db(&self) -> &::salsa::Db {
        &self.db
    }
}

impl<Devsoul: IsDevsoul> Default for DevComptime<Devsoul>
where
    Devsoul::Linktime: Default,
{
    fn default() -> Self {
        Self {
            target: DevComptimeTarget::None,
            db: Default::default(),
            linktime: Default::default(),
            target_path: None,
        }
    }
}
