pub mod constructors;
pub mod final_destination;
pub mod toolchain;

use self::term::{
    abstract_variable::EthAbstractVariable,
    application::{EthApplication, TermFunctionReduced},
    curry::EthCurry,
    ritchie::EthRitchie,
};
use super::*;
use husky_entity_path::path::major_item::{trai::TraitPath, ty::TypePath};
use husky_vfs::toolchain::Toolchain;

impl EthTerm {
    pub fn leading_ty_path(self, db: &::salsa::Db) -> Option<TypePath> {
        match self.application_expansion(db).function() {
            TermFunctionReduced::TypeOntology(path) => Some(path),
            _ => None,
        }
    }

    pub fn leading_trai_path(self, db: &::salsa::Db) -> Option<TraitPath> {
        match self.application_expansion(db).function() {
            TermFunctionReduced::Trait(path) => Some(path),
            _ => None,
        }
    }

    /// see `self` as the type of another term, return the type expectation for that term
    pub fn ty_expectation(
        self,
        db: &::salsa::Db,
    ) -> EthTermResult<TypeFinalDestinationExpectation> {
        Ok(match self.application_expansion(db).function() {
            TermFunctionReduced::TypeOntology(path) => {
                TypeFinalDestinationExpectation::EqsNonSortTypePath(path)
            }
            _ => TypeFinalDestinationExpectation::Any,
        })
    }

    pub fn synthesize_function_application_expr_ty(
        db: &::salsa::Db,
        variance: Variance,
        parameter_symbol: Option<EthTerm>,
        parameter_ty: EthTerm,
        return_ty: EthTerm,
        argument_ty: EthTerm,
        shift: i8,
    ) -> EthTermResult<EthTerm> {
        if shift == 0 {
            if parameter_symbol.is_some() {
                todo!()
            }
            return Ok(return_ty);
        }
        if parameter_symbol.is_some() {
            todo!()
        }
        match argument_ty {
            EthTerm::Curry(argument_ty) => {
                let expr_ty = Self::synthesize_function_application_expr_ty(
                    db,
                    variance,
                    parameter_symbol,
                    parameter_ty,
                    return_ty,
                    argument_ty.return_ty(db),
                    shift - 1,
                )?;
                Ok(EthCurry::new(
                    argument_ty.toolchain(db),
                    argument_ty.curry_kind(db),
                    argument_ty.variance(db),
                    None,
                    argument_ty.parameter_ty(db),
                    expr_ty,
                    db,
                )
                .into())
            }
            _ => unreachable!(),
        }
    }

    pub fn new_ty_ontology(
        db: &::salsa::Db,
        path: TypePath,
        arguments: impl IntoIterator<Item = EthTerm>,
    ) -> EthTermResult<Self> {
        let mut term: Self = ItemPathTerm::TypeOntology(path).into();
        for argument in arguments {
            term = EthApplication::new(db, term, argument)?
        }
        Ok(term)
    }
}

impl EthAbstractVariable {
    fn toolchain(self, db: &::salsa::Db) -> Option<Toolchain> {
        self.ty(db).toolchain(db)
    }
}

#[salsa::tracked]
pub(crate) fn ethereal_term_curry_toolchain(db: &::salsa::Db, term: EthCurry) -> Option<Toolchain> {
    let mut merger = ToolchainMerger::default();
    if let Some(parameter_hvar) = term.parameter_hvar(db) {
        merger.accept(parameter_hvar.toolchain(db))
    }
    merger.accept(term.parameter_ty(db).toolchain(db));
    merger.accept(term.return_ty(db).toolchain(db));
    merger.finish()
}

#[salsa::tracked]
pub(crate) fn ethereal_term_application_toolchain(
    db: &::salsa::Db,
    term: EthApplication,
) -> Option<Toolchain> {
    let mut merger = ToolchainMerger::default();
    merger.accept(term.function(db).toolchain(db));
    merger.accept(term.argument(db).toolchain(db));
    merger.finish()
}

#[salsa::tracked]
pub(crate) fn ethereal_term_ritchie_toolchain(
    db: &::salsa::Db,
    term: EthRitchie,
) -> Option<Toolchain> {
    let mut merger = ToolchainMerger::default();
    for parameter_contracted_ty in term.parameter_contracted_tys(db) {
        merger.accept(parameter_contracted_ty.ty().toolchain(db))
    }
    merger.accept(term.return_ty(db).toolchain(db));
    merger.finish()
}

#[derive(Debug, Default)]
struct ToolchainMerger {
    toolchain: Option<Toolchain>,
}

impl ToolchainMerger {
    fn accept(&mut self, toolchain: Option<Toolchain>) {
        match (self.toolchain, toolchain) {
            (_, None) => (),
            (None, Some(_)) => self.toolchain = toolchain,
            (Some(self_toolchain), Some(toolchain)) => assert_eq!(self_toolchain, toolchain),
        }
    }

    fn finish(self) -> Option<Toolchain> {
        self.toolchain
    }
}
