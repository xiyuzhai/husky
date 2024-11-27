#[path = "crate/lib.rs"]
pub mod lib;
#[path = "crate/main.rs"]
pub mod main;
#[path = "crate/requirements.rs"]
pub mod requirements;
#[path = "crate/task.rs"]
pub mod task;

use self::lib::*;
use self::main::*;
use self::requirements::*;
use self::task::*;
use super::*;
use husky_vfs::path::crate_path::{CrateKind, CratePath};

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CrateSynNodeDecl {
    Lib(LibCrateSynNodeDecl),
    Main(MainCrateSynNodeDecl),
    Requirements(RequirementsCrateSynNodeDecl),
    Task(TaskCrateSynNodeDecl),
}

impl HasSynNodeDecl for CratePath {
    type NodeDecl = Option<CrateSynNodeDecl>;

    fn syn_node_decl<'a>(self, db: &'a salsa::Db) -> Self::NodeDecl {
        crate_syn_node_decl(db, self)
    }
}

#[salsa::tracked]
fn crate_syn_node_decl(db: &::salsa::Db, crate_path: CratePath) -> Option<CrateSynNodeDecl> {
    let parser = CrateDeclParser::new(db, crate_path)?;
    Some(parser.parse_crate_syn_node_decl())
}

impl<'db> CrateDeclParser<'db> {
    fn parse_crate_syn_node_decl(self) -> CrateSynNodeDecl {
        let db = self.db();
        match self.crate_path().kind(db) {
            CrateKind::Lib => self.parse_lib_crate_syn_node_decl().into(),
            CrateKind::Main => self.parse_main_crate_syn_node_decl().into(),
            CrateKind::Requirements => self.parse_requirements_crate_syn_node_decl().into(),
            CrateKind::Task => self.parse_task_crate_syn_node_decl().into(),
            CrateKind::Bin(_) => todo!(),
            CrateKind::IntegratedTest(_) => todo!(),
            CrateKind::Example => todo!(),
        }
    }
}

#[test]
fn crate_syn_node_decl_works() {
    DB::ast_rich_test_debug_with_db(
        crate_syn_node_decl,
        &AstTestConfig::new(
            "crate_syn_node_decl",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    )
}

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CrateSynDecl {
    Lib(LibCrateSynDecl),
    Main(MainCrateSynDecl),
    Requirements(RequirementsCrateSynDecl),
    Task(TaskCrateSynDecl),
}

impl CrateSynDecl {
    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            CrateSynDecl::Lib(slf) => slf.syn_expr_region(db),
            CrateSynDecl::Main(slf) => slf.syn_expr_region(db),
            CrateSynDecl::Requirements(slf) => slf.syn_expr_region(db),
            CrateSynDecl::Task(slf) => slf.syn_expr_region(db),
        }
    }
}

impl HasSynDecl for CratePath {
    type Decl = Option<CrateSynDecl>;

    fn syn_decl<'a>(self, db: &'a salsa::Db) -> SynDeclResult<Self::Decl> {
        crate_syn_decl(db, self)
    }
}

#[salsa::tracked]
fn crate_syn_decl(db: &::salsa::Db, crate_path: CratePath) -> SynDeclResult<Option<CrateSynDecl>> {
    let Some(syn_node_decl) = crate_path.syn_node_decl(db) else {
        return Ok(None);
    };
    Ok(Some(match syn_node_decl {
        CrateSynNodeDecl::Lib(syn_node_decl) => {
            LibCrateSynDecl::from_node(crate_path, syn_node_decl, db)?.into()
        }
        CrateSynNodeDecl::Main(syn_node_decl) => {
            MainCrateSynDecl::from_node(crate_path, syn_node_decl, db)?.into()
        }
        CrateSynNodeDecl::Requirements(syn_node_decl) => {
            RequirementsCrateSynDecl::from_node(crate_path, syn_node_decl, db)?.into()
        }
        CrateSynNodeDecl::Task(syn_node_decl) => {
            TaskCrateSynDecl::from_node(crate_path, syn_node_decl, db)?.into()
        }
    }))
}

#[test]
fn crate_syn_decl_works() {
    DB::ast_rich_test_debug_with_db(
        crate_syn_decl,
        &AstTestConfig::new(
            "crate_syn_decl",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    )
}
