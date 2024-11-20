use crate::*;
use convert_case::{Case, Casing};
use lean_item_path::namespace::LnNamespace;
use visored_item_path::module::{VdModulePath, VdModulePathData};
use visored_prelude::division::VdDivisionLevel;

#[salsa::tracked]
pub fn vd_module_path_to_ln_namespace(
    db: &::salsa::Db,
    module_path: VdModulePath,
) -> Option<LnNamespace> {
    match module_path.data(db) {
        VdModulePathData::Root(_) => Some(LnNamespace::new_root(db)),
        VdModulePathData::Division {
            parent,
            division_kind,
            disambiguator,
        } => {
            match division_kind {
                VdDivisionLevel::Part => (),
                VdDivisionLevel::Chapter => (),
                VdDivisionLevel::Section => (),
                VdDivisionLevel::Subsection => (),
                VdDivisionLevel::Subsubsection => (),
                VdDivisionLevel::Stmts => return None,
            }
            let parent_namespace = vd_module_path_to_ln_namespace_or_inherited(db, parent);
            Some(parent_namespace.child(
                format!(
                    "{}{}",
                    division_kind.uppercase_code_name(),
                    disambiguator + 1
                ),
                db,
            ))
        }
        VdModulePathData::Paragraph {
            parent,
            disambiguator,
        } => None,
        VdModulePathData::Environment {
            parent,
            environment_path,
            disambiguator,
        } => {
            let parent_namespace = vd_module_path_to_ln_namespace_or_inherited(db, parent);
            Some(parent_namespace.child(
                format!(
                    "{}{}",
                    environment_path.name().coword().data(db).to_case(Case::Pascal),
                    disambiguator+1
                ),
                db,
            ))
        }
    }
}

#[salsa::tracked]
pub fn vd_module_path_to_ln_namespace_or_inherited(
    db: &::salsa::Db,
    module_path: VdModulePath,
) -> LnNamespace {
    match module_path.data(db) {
        VdModulePathData::Root(lx_file_path) => LnNamespace::new_root(db),
        VdModulePathData::Division {
            parent,
            division_kind,
            disambiguator,
        } => {
            let parent_namespace = vd_module_path_to_ln_namespace_or_inherited(db, parent);
            match division_kind {
                VdDivisionLevel::Part => (),
                VdDivisionLevel::Chapter => (),
                VdDivisionLevel::Section => (),
                VdDivisionLevel::Subsection => (),
                VdDivisionLevel::Subsubsection => (),
                VdDivisionLevel::Stmts => return parent_namespace,
            }
            parent_namespace.child(
                format!(
                    "{}{}",
                    division_kind.uppercase_code_name(),
                    disambiguator + 1
                ),
                db,
            )
        }
        VdModulePathData::Paragraph {
            parent,
            disambiguator,
        } => todo!(),
        VdModulePathData::Environment {
            parent,
            environment_path,
            disambiguator,
        } => {
            let parent_namespace = vd_module_path_to_ln_namespace_or_inherited(db, parent);
            parent_namespace.child(
                format!(
                    "{}{}",
                    environment_path
                        .name()
                        .coword()
                        .data(db)
                        .to_case(Case::Pascal),
                    disambiguator + 1
                ),
                db,
            )
        }
    }
}
