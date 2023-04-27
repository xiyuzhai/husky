mod expansion;
mod reduction;
mod utils;

pub use self::expansion::*;
pub use self::reduction::*;

use super::*;
use std::fmt::{Debug, Display};

/// in husky, application is generalized to include composition as a special case;
///
/// when shift is `0`, this is the normal application;
///
/// when shift is `1`, this is composition,
///
/// in general when shift is `n`, this is equavalent to
///
/// use abstraction `n` times, and then apply original argument to them,
///
/// then apply function to the result,
///
/// `\x1 ... \xn -> $function ($argument \x1 ... \xn)`
#[salsa::interned(db = EtherealTermDb, jar = EtherealTermJar, constructor = new_inner)]
pub struct EtherealTermApplication {
    pub function: EtherealTerm,
    pub argument: EtherealTerm,
    pub shift: u8,
}

#[test]
fn term_application_size_works() {
    assert_eq!(
        std::mem::size_of::<EtherealTermApplication>(),
        std::mem::size_of::<u32>()
    );
}

impl EtherealTermApplication {
    //// this constructor guarantees that the result is reduced and first-order valid
    /// returns EtherealTerm instead of EtherealTermApplication because it might reduce to a non application term
    pub fn new(
        db: &dyn EtherealTermDb,
        function: EtherealTerm,
        argument: EtherealTerm,
    ) -> EtherealTermResult<EtherealTerm> {
        let (function_parameter_ty_total_number_of_curry_parameters, argument_expectation) = {
            match function.raw_ty(db)? {
                RawType::Declarative(DeclarativeTerm::Curry(function_declarative_ty)) => {
                    let parameter_ty = function_declarative_ty.parameter_ty(db);
                    let function_parameter_ty_total_number_of_curry_parameters =
                        parameter_ty.total_number_of_curry_parameters(db);
                    let argument_expectation =
                        parameter_ty_raw_term_to_argument_ty_expectation(db, parameter_ty);
                    (
                        function_parameter_ty_total_number_of_curry_parameters,
                        argument_expectation,
                    )
                }
                RawType::Ethereal(EtherealTerm::Curry(_)) => todo!(),
                _ => return Err(todo!()),
            }
        };
        let argument_ty_total_number_of_curry_parameters =
            argument.ty_total_number_of_curry_parameters(db)?;
        if argument_ty_total_number_of_curry_parameters
            < function_parameter_ty_total_number_of_curry_parameters
        {
            todo!()
        }
        let shift = argument_ty_total_number_of_curry_parameters
            - function_parameter_ty_total_number_of_curry_parameters;
        let term = Self::new_unchecked(db, function, argument, shift);
        Ok(term)
    }

    //// this constructor guarantees that the result is reduced, not necessarily valid
    /// returns EtherealTerm instead of EtherealTermApplication because it might reduce to a non application term
    pub(super) fn new_unchecked(
        db: &dyn EtherealTermDb,
        function: EtherealTerm,
        argument: EtherealTerm,
        shift: u8,
    ) -> EtherealTerm {
        Self::new_inner(db, function, argument, shift).reduce(db)
    }

    /// returns EtherealTerm instead of EtherealTermApplication because it might reduce to a non application term
    pub(crate) fn from_declarative(
        db: &dyn EtherealTermDb,
        raw_term_application: DeclarativeTermExplicitApplication,
        term_ty_expectation: TermTypeExpectation,
    ) -> EtherealTermResult<EtherealTerm> {
        // todo: implicit arguments
        term_uncheck_from_raw_term_application(db, raw_term_application, term_ty_expectation)
    }

    pub(crate) fn declarative_ty(
        self,
        db: &dyn EtherealTermDb,
    ) -> EtherealTermResult<DeclarativeTerm> {
        term_application_declarative_ty(db, self)
    }

    pub(crate) fn show_with_db_fmt(
        self,
        f: &mut std::fmt::Formatter<'_>,
        db: &dyn EtherealTermDb,
        ctx: &mut TermShowContext,
    ) -> std::fmt::Result {
        self.function(db).show_with_db_fmt(f, db, ctx)?;
        f.write_str(" ")?;
        self.argument(db).show_with_db_fmt(f, db, ctx)
    }
}

#[salsa::tracked(jar = EtherealTermJar)]
pub(crate) fn term_uncheck_from_raw_term_application(
    db: &dyn EtherealTermDb,
    raw_term_application: DeclarativeTermExplicitApplication,
    declarative_ty_expectation: TermTypeExpectation,
) -> EtherealTermResult<EtherealTerm> {
    // todo: implicit arguments
    term_uncheck_from_raw_term_application_aux(
        db,
        EtherealTerm::from_declarative(
            db,
            raw_term_application.function(db),
            declarative_ty_expectation,
        )?,
        raw_term_application.argument(db),
        declarative_ty_expectation,
    )
}

/// argument is `DeclarativeTerm` instead of `EtherealTerm` is because we need to read function type to get expectation for argument
pub(crate) fn term_uncheck_from_raw_term_application_aux(
    db: &dyn EtherealTermDb,
    function: EtherealTerm,
    argument: DeclarativeTerm,
    declarative_ty_expectation: TermTypeExpectation,
) -> EtherealTermResult<EtherealTerm> {
    // todo: implicit arguments
    let (function_parameter_ty_total_number_of_curry_parameters, argument_expectation) = {
        match function.raw_ty(db)? {
            RawType::Declarative(DeclarativeTerm::Curry(function_declarative_ty)) => {
                let parameter_ty = function_declarative_ty.parameter_ty(db);
                let function_parameter_ty_total_number_of_curry_parameters =
                    parameter_ty.total_number_of_curry_parameters(db);
                let argument_expectation =
                    parameter_ty_raw_term_to_argument_ty_expectation(db, parameter_ty);
                (
                    function_parameter_ty_total_number_of_curry_parameters,
                    argument_expectation,
                )
            }
            RawType::Ethereal(_) => todo!(),
            _ => todo!(),
        }
    };
    let argument = EtherealTerm::from_declarative(db, argument, argument_expectation)?;
    let argument_ty_total_number_of_curry_parameters =
        argument.ty_total_number_of_curry_parameters(db)?;
    if argument_ty_total_number_of_curry_parameters
        < function_parameter_ty_total_number_of_curry_parameters
    {
        todo!()
    }
    let shift = argument_ty_total_number_of_curry_parameters
        - function_parameter_ty_total_number_of_curry_parameters;
    Ok(EtherealTermApplication::new_unchecked(
        db, function, argument, shift,
    ))
}

fn parameter_ty_raw_term_to_argument_ty_expectation(
    db: &dyn EtherealTermDb,
    raw_term: DeclarativeTerm,
) -> TermTypeExpectation {
    match raw_term {
        DeclarativeTerm::EntityPath(DeclarativeTermEntityPath::Type(path)) => {
            TermTypeExpectation::FinalDestinationEqsNonSortTypePath(path)
        }
        DeclarativeTerm::Category(_) => TermTypeExpectation::FinalDestinationEqsSort,
        DeclarativeTerm::Curry(_) => todo!(),
        DeclarativeTerm::ExplicitApplication(_) => todo!(),
        _ => TermTypeExpectation::Any,
    }
}

#[salsa::tracked(jar = EtherealTermJar)]
pub(crate) fn parameter_ty_raw_term_curry_to_argument_ty_expectation(
    db: &dyn EtherealTermDb,
    raw_term_curry: DeclarativeTermCurry,
) -> TermTypeExpectation {
    todo!()
}
#[salsa::tracked(jar = EtherealTermJar)]
pub(crate) fn parameter_ty_raw_term_application_to_argument_ty_expectation(
    db: &dyn EtherealTermDb,
) -> TermTypeExpectation {
    todo!()
}

#[salsa::tracked(jar = EtherealTermJar)]
pub(crate) fn term_application_declarative_ty(
    db: &dyn EtherealTermDb,
    term_application: EtherealTermApplication,
) -> EtherealTermResult<DeclarativeTerm> {
    let function = term_application.function(db);
    let argument = term_application.argument(db);
    let function_declarative_ty = match function.raw_ty(db)? {
        RawType::Declarative(DeclarativeTerm::Curry(function_declarative_ty)) => {
            function_declarative_ty
        }
        RawType::Ethereal(EtherealTerm::Curry(_)) => todo!(),
        _ => return Err(todo!()),
    };
    Ok(match function_declarative_ty.parameter_variable(db) {
        Some(_) => todo!(),
        None => function_declarative_ty.return_ty(db),
    })
}

impl EtherealTerm {
    fn ty_total_number_of_curry_parameters(
        self,
        db: &dyn EtherealTermDb,
    ) -> EtherealTermResult<u8> {
        Ok(match self.raw_ty(db)? {
            RawType::Declarative(ty) => ty.total_number_of_curry_parameters(db),
            RawType::Ethereal(ty) => ty.total_number_of_curry_parameters(db),
            _ => 0,
        })
    }
}

impl<Db: EtherealTermDb + ?Sized> salsa::DisplayWithDb<Db> for EtherealTermApplication {
    fn display_with_db_fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &Db,
        level: salsa::DisplayFormatLevel,
    ) -> std::fmt::Result {
        let db = <Db as salsa::DbWithJar<EtherealTermJar>>::as_jar_db(db);
        self.show_with_db_fmt(f, db, &mut Default::default())
    }
}

impl EtherealTermApplication {
    fn substitute(self, db: &dyn EtherealTermDb, substituation: &TermSubstitution) -> EtherealTerm
    where
        Self: Copy,
    {
        todo!()
        // let old_m = self.function(db);
        // let m = old_m.substitute(db, substituation);
        // let old_n = self.argument(db);
        // let n = old_n.substitute(db, substituation);
        // if old_m == m && old_n == n {
        //     return self;
        // }
        // EtherealTermApplication::new(db, m, n, self.shift(db))
    }
}

impl std::fmt::Display for EtherealTermApplication {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}