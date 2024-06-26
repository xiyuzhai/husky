mod libraries;
mod linkage_impls;

use self::linkage_impls::generate_linkage_impls;
use self::{libraries::MonoLinkageLibraries, linkage_impls::LinkageImplMap};
use crate::*;
use husky_linkage::version_stamp::LinkageVersionStamp;
use husky_vfs::path::linktime_target_path::LinktimeTargetPath;
use version_stamp::HasVersionStamp;

pub struct MonoLinktimeInternal<LinkageImpl>
where
    LinkageImpl: IsLinkageImpl,
{
    target_path: LinktimeTargetPath,
    /// this is needed to kep Box<dyn StaticDyn> valid
    past_libraries: Vec<MonoLinkageLibraries>,
    libraries: MonoLinkageLibraries,
    linkage_impls: LinkageImplMap<LinkageImpl>,
}

impl<LinkageImpl: IsLinkageImpl> MonoLinktimeInternal<LinkageImpl>
where
    LinkageImpl: IsLinkageImpl,
{
    pub(crate) fn new(target_path: LinktimeTargetPath, db: &::salsa::Db) -> Self {
        let Ok(libraries) = MonoLinkageLibraries::generate(target_path, db) else {
            todo!("error in generating libraries")
        };
        let linkage_impls = generate_linkage_impls(target_path, &libraries, db);
        Self {
            target_path,
            past_libraries: vec![],
            libraries,
            linkage_impls,
        }
    }

    pub(crate) fn get_linkage_impl(
        &self,
        linkage: Linkage,
        db: &::salsa::Db,
    ) -> Option<LinkageImpl> {
        let Some(&(version_stamp, linkage_impl)) = self.linkage_impls.get(&linkage) else {
            use husky_print_utils::p;
            use salsa::DebugWithDb;
            let _linkages: Vec<Linkage> = self.linkage_impls.clone().into_keys().collect();
            // let old_linkage: Linkage = unsafe { std::mem::transmute(194u32) };
            // let LinkageData::UnveilAssocFunctionRitchie {
            //     path: old_path,
            //     instantiation: old_instantiation,
            // } = old_linkage.data(db)
            // else {
            //     unreachable!()
            // };
            // let LinkageData::UnveilAssocFunctionRitchie {
            //     path,
            //     instantiation,
            // } = linkage.data(db)
            // else {
            //     unreachable!()
            // };
            p!(linkage.debug(db), linkage);
            unreachable!()
        };
        (version_stamp == linkage.version_stamp(db)).then_some(linkage_impl)
    }

    /// still need the key to avoid redundant reload when two attempts simultaneously want to lock
    pub(crate) fn get_linkage_impl_with_reload(
        &mut self,
        key: Linkage,
        db: &::salsa::Db,
    ) -> LinkageImpl {
        let (deps, linkage) = self
            .linkage_impls
            .get(&key)
            .copied()
            .expect("should be some");
        if deps == key.version_stamp(db) {
            return linkage;
        }
        self.reload(db);
        self.linkage_impls
            .get(&key)
            .copied()
            .expect("should be some")
            .1
    }

    fn reload(&mut self, db: &::salsa::Db) {
        let libraries = std::mem::replace(
            &mut self.libraries,
            MonoLinkageLibraries::generate(self.target_path, db).unwrap(),
        );
        self.past_libraries.push(libraries);
        self.linkage_impls = generate_linkage_impls(self.target_path, &self.libraries, db)
    }
}
