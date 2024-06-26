use crate::*;

use husky_ast::DefnBlock;
use husky_vfs::path::module_path::SubmodulePath;
use vec_like::VecSet;

#[salsa::tracked(return_ref)]
pub(crate) fn submodules(db: &::salsa::Db, module_path: ModulePath) -> Vec<SubmodulePath> {
    let ast_sheet = module_path.ast_sheet(db);
    ast_sheet
        .top_level_asts_iter()
        .filter_map(|ast| match ast {
            AstData::Identifiable { block, .. } => match block {
                DefnBlock::Submodule { path, .. } => Some(path.submodule_path(db)),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// all modules, must be included in module tree
#[salsa::tracked(return_ref)]
pub(crate) fn all_modules_within_crate(
    db: &::salsa::Db,
    crate_path: CratePath,
) -> VecSet<ModulePath> {
    let root = crate_path.root_module_path(db);
    let mut all_modules = VecSet::default();
    all_modules.insert(root);
    collect_all_modules(db, root, &mut all_modules);
    all_modules
}

fn collect_all_modules(db: &::salsa::Db, root: ModulePath, all_modules: &mut VecSet<ModulePath>) {
    for submodule in submodules(db, root) {
        all_modules.insert(**submodule);
        collect_all_modules(db, **submodule, all_modules)
    }
}

#[test]
fn submodules_works() {
    DB::ast_rich_test_debug_with_db(
        |db, module_path| db.submodules(module_path),
        &AstTestConfig::new(
            "submodules",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    )
}

#[test]
fn all_modules_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| EntityTreeDb::all_modules_within_crate(db, crate_path),
        &AstTestConfig::new(
            "all_modules_within_crate",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    )
}
