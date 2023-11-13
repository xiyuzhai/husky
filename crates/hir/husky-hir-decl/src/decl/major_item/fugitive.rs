mod r#fn;
mod gn;
mod ty_alias;
mod val;

use husky_syn_decl::FugitiveSynDecl;

pub use self::gn::*;
pub use self::r#fn::*;
pub use self::ty_alias::*;
pub use self::val::*;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::debug_with_db(db = HirDeclDb)]
#[enum_class::from_variants]
pub enum FugitiveHirDecl {
    FunctionFn(FunctionFnFugitiveHirDecl),
    Val(ValFugitiveHirDecl),
    FunctionGn(FunctionGnFugitiveHirDecl),
    TypeAlias(TypeAliasHirDecl),
}

impl FugitiveHirDecl {
    pub fn template_parameters<'a>(self, db: &'a dyn HirDeclDb) -> &'a [HirTemplateParameter] {
        match self {
            FugitiveHirDecl::FunctionFn(decl) => decl.template_parameters(db),
            FugitiveHirDecl::Val(_decl) => &[],
            FugitiveHirDecl::FunctionGn(decl) => decl.template_parameters(db),
            FugitiveHirDecl::TypeAlias(_) => todo!(),
        }
    }

    // pub fn hir_expr_region(self, db: &dyn HirDeclDb) -> HirExprRegion {
    //     match self {
    //         FugitiveHirDecl::Fn(decl) => decl.hir_expr_region(db).into(),
    //         FugitiveHirDecl::Val(decl) => decl.hir_expr_region(db).into(),
    //         FugitiveHirDecl::Gn(decl) => decl.hir_expr_region(db).into(),
    //     }
    // }

    pub fn path(self, db: &dyn HirDeclDb) -> FugitivePath {
        match self {
            FugitiveHirDecl::FunctionFn(decl) => decl.path(db),
            FugitiveHirDecl::Val(decl) => decl.path(db),
            FugitiveHirDecl::FunctionGn(decl) => decl.path(db),
            FugitiveHirDecl::TypeAlias(decl) => decl.path(db),
        }
    }
}

impl HasHirDecl for FugitivePath {
    type HirDecl = FugitiveHirDecl;

    fn hir_decl(self, db: &dyn HirDeclDb) -> Option<Self::HirDecl> {
        fugitive_hir_decl(db, self)
    }
}

#[salsa::tracked(jar = HirDeclJar)]
fn fugitive_hir_decl(db: &dyn HirDeclDb, path: FugitivePath) -> Option<FugitiveHirDecl> {
    match path.syn_decl(db).expect("no errors for hir stage") {
        FugitiveSynDecl::FunctionFn(syn_decl) => {
            Some(FunctionFnFugitiveHirDecl::from_syn(path, syn_decl, db).into())
        }
        FugitiveSynDecl::Val(syn_decl) => {
            Some(ValFugitiveHirDecl::from_syn(path, syn_decl, db).into())
        }
        FugitiveSynDecl::FunctionGn(syn_decl) => {
            Some(FunctionGnFugitiveHirDecl::from_syn(path, syn_decl, db).into())
        }
    }
}