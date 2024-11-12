mod adversarial;
mod adversarial_generator;
mod adversarial_manager;
mod edit;

use self::adversarial::*;
use self::adversarial_generator::*;
use self::adversarial_manager::*;
use self::edit::*;
use super::*;
use husky_rng_utils::XRng;
use lock::RichTestLock;
use salsa::DebugWithDb;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdversarialKind {
    Vfs,
    TokenData,
    Ast,
}

impl AdversarialKind {
    pub fn as_str(self) -> &'static str {
        match self {
            AdversarialKind::Vfs => "vfs",
            AdversarialKind::TokenData => "token",
            AdversarialKind::Ast => "ast",
        }
    }
}

impl std::fmt::Display for AdversarialKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

pub(super) fn vfs_adversarial_test<M, U, R>(
    db: &mut Db,
    package_adversarials_dir: &Path,
    unit: U,
    f: &impl Fn(&::salsa::Db, U) -> R,
    config: &VfsTestConfig,
    lock: &mut RichTestLock,
) where
    U: IsVfsTestUnit<M> + ::salsa::DebugWithDb,
{
    // let Some(adversarial_path) =
    //     unit.determine_adversarial_path(db, AdversarialKind::Vfs, package_adversarials_dir, config)
    // else {
    //     return;
    // };
    // // TODO: use rich test lock
    // //     if let Some(old_usage) =
    // //         paths_used.insert(adversarial_path.clone(), PathUsage::Adversarial(unit))
    // //     {
    // //         panic!(
    // //             r#"Detect conflicting path for unit `{:?}` while doing adversarial testing!
    // // Old usage is `{:?}`.
    // // The conflicting path is `{adversarial_path:?}`"#,
    // //             unit.debug(db),
    // //             old_usage.debug(db),
    // //         )
    // //     }
    // let Some(module) = unit.vfs_test_unit_downcast_as_module_path() else {
    //     // ad hoc, what to do here?
    //     // for things like item syn node path, adversarial attack might make the entity tree change
    //     // we might want something that avoids changing the entity tree
    //     return;
    // };
    // let manager = VfsAdversarialManager::new(module, adversarial_path);
    // manager.run(db, &|db| {
    //     f(db, unit);
    // })
}
