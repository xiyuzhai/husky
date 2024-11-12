mod expansion;
pub mod reduction;

pub use self::expansion::*;

use super::*;
use std::fmt::Debug;

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
#[salsa::interned(constructor = new_inner)]
pub struct EthApplication {
    pub function: EthTerm,
    pub argument: EthTerm,
    pub shift: u8,
}

#[test]
fn term_application_size_works() {
    assert_eq!(
        std::mem::size_of::<EthApplication>(),
        std::mem::size_of::<u32>()
    );
}

impl EthApplication {
    //// this constructor guarantees that the result is reduced and first-order valid
    /// returns EthTerm instead of EthTermApplication because it might reduce to a non application term
    pub fn new(db: &::salsa::Db, function: EthTerm, argument: EthTerm) -> EthTermResult<EthTerm> {
        let (function_parameter_ty_curry_parameter_count, _argument_expectation) = {
            match function.raw_ty(db)? {
                RawType::Declarative(DecTerm::Curry(function_declarative_ty)) => {
                    let parameter_ty = function_declarative_ty.parameter_ty(db);
                    (
                        parameter_ty.curry_parameter_count(db),
                        parameter_ty.ty_final_destination_expectation(db)?,
                    )
                }
                _ => Err(EthTermError::ExpectedCurryForApplicationFunctionType)?,
            }
        };
        let argument_ty_curry_parameter_count = argument.ty_curry_parameter_count(db)?;
        if argument_ty_curry_parameter_count < function_parameter_ty_curry_parameter_count {
            todo!()
        }
        let shift = argument_ty_curry_parameter_count - function_parameter_ty_curry_parameter_count;
        let term = Self::new_reduced(db, function, argument, shift);
        Ok(term)
    }

    /// this constructor guarantees that the result is reduced, not necessarily valid
    /// returns EthTerm instead of EthTermApplication because it might reduce to a non application term
    pub(super) fn new_reduced(
        db: &::salsa::Db,
        function: EthTerm,
        argument: EthTerm,
        shift: u8,
    ) -> EthTerm {
        Self::new_inner(db, function, argument, shift).reduce(db)
    }

    /// returns EthTerm instead of EthTermApplication because it might reduce to a non application term
    pub(crate) fn from_dec(
        db: &::salsa::Db,
        declarative_term_application: DecApplication,
        term_ty_expectation: TypeFinalDestinationExpectation,
    ) -> EthTermResult<EthTerm> {
        // todo: implicit arguments
        ethereal_term_from_dec_term_application(
            db,
            declarative_term_application,
            term_ty_expectation,
        )
    }

    pub(crate) fn declarative_ty(self, db: &::salsa::Db) -> EthTermResult<DecTerm> {
        ethereal_term_application_declarative_ty(db, self)
    }
}

#[salsa::tracked]
pub(crate) fn ethereal_term_from_dec_term_application(
    db: &::salsa::Db,
    declarative_term_application: DecApplication,
    declarative_ty_expectation: TypeFinalDestinationExpectation,
) -> EthTermResult<EthTerm> {
    // todo: implicit arguments
    term_uncheck_from_dec_term_application_aux(
        db,
        EthTerm::from_dec(
            db,
            declarative_term_application.function(db),
            declarative_ty_expectation,
        )?,
        declarative_term_application.argument(db),
        declarative_ty_expectation,
    )
}

/// argument is `DecTerm` instead of `EthTerm` is because we need to read function type to get expectation for argument
///
pub(crate) fn term_uncheck_from_dec_term_application_aux(
    db: &::salsa::Db,
    function: EthTerm,
    argument: DecTerm,
    _declarative_ty_expectation: TypeFinalDestinationExpectation,
) -> EthTermResult<EthTerm> {
    // todo: implicit arguments
    let (function_parameter_ty_curry_parameter_count, argument_expectation) = {
        match function.raw_ty(db)? {
            RawType::Declarative(DecTerm::Curry(function_ty)) => {
                let parameter_ty = function_ty.parameter_ty(db);
                (
                    parameter_ty.curry_parameter_count(db),
                    parameter_ty.ty_final_destination_expectation(db)?,
                )
            }
            _ => Err(EthTermError::ExpectedCurryForApplicationFunctionType)?,
        }
    };
    let argument = EthTerm::from_dec(db, argument, argument_expectation)?;
    let argument_ty_curry_parameter_count = argument.ty_curry_parameter_count(db)?;
    if argument_ty_curry_parameter_count < function_parameter_ty_curry_parameter_count {
        todo!()
    }
    let shift = argument_ty_curry_parameter_count - function_parameter_ty_curry_parameter_count;
    Ok(EthApplication::new_reduced(db, function, argument, shift))
}

#[salsa::tracked]
pub(crate) fn ethereal_term_application_declarative_ty(
    db: &::salsa::Db,
    term_application: EthApplication,
) -> EthTermResult<DecTerm> {
    let function = term_application.function(db);
    let argument = term_application.argument(db);
    match function.raw_ty(db)? {
        RawType::Declarative(DecTerm::Curry(function_ty)) => match function_ty.parameter_hvar(db) {
            Some(function_ty_parameter_variable) => {
                ethereal_term_application_declarative_ty_dependent_aux(
                    db,
                    function_ty,
                    function_ty_parameter_variable,
                    argument.into_declarative(db),
                    argument.raw_ty(db)?,
                    term_application.shift(db),
                )
            }
            None => ethereal_term_application_declarative_ty_nondependent_aux(
                db,
                function_ty,
                argument.raw_ty(db)?,
                term_application.shift(db),
            ),
        },
        _ => Err(EthTermError::ExpectedCurryForApplicationFunctionType)?,
    }
}

/// function_ty.parameter_hvar(db) matches Some
pub(crate) fn ethereal_term_application_declarative_ty_dependent_aux(
    db: &::salsa::Db,
    function_ty: DecCurry,
    function_ty_parameter_variable: DecAbstractVariable,
    argument: DecTerm,
    argument_ty: RawType,
    shift: u8,
) -> EthTermResult<DecTerm> {
    // for example, suppose that
    //
    // function_ty = (a: A) -> List a
    // function_ty_parameter_variable = a
    match shift {
        0 => Ok(function_ty.return_ty(db).substitute_copy(
            db,
            &DecTermSubstitution::new(function_ty_parameter_variable, argument),
        )),
        shift => {
            // argument = arg
            // argument_ty = (b: B) -> C b -> A
            // shift = 2
            // then the type of the shifted application should be
            // (b: B) -> (c: C b) -> List (arg b c)
            // b, c are first created as ad hoc symbols
            // then converted to variables
            match argument_ty {
                RawType::Declarative(DecTerm::Curry(argument_ty)) => {
                    let new_parameter_ty = argument_ty.parameter_ty(db);
                    // shift is used as disambiguator
                    // this is possible because we expect in the recursion process
                    // shift never appears twice
                    let new_parameter_symbol = unsafe {
                        DecSymbolicVariable::new_ad_hoc(
                            db,
                            argument_ty.toolchain(db),
                            new_parameter_ty,
                            shift,
                        )
                    };
                    Ok(DecCurry::new_dependent(
                        db,
                        argument_ty.toolchain(db),
                        argument_ty.curry_kind(db),
                        argument_ty.variance(db),
                        new_parameter_symbol,
                        new_parameter_ty,
                        ethereal_term_application_declarative_ty_dependent_aux(
                            db,
                            function_ty,
                            function_ty_parameter_variable,
                            // corresponds to `arg b` in the example
                            DecApplication::new(db, argument, new_parameter_symbol.into()).into(),
                            // corresponds to be `C b -> A` in the example
                            argument_ty
                                .return_ty_with_variable_substituted(
                                    db,
                                    new_parameter_symbol.into(),
                                )
                                .into(),
                            shift - 1,
                        )?,
                    )
                    .into())
                }
                _ => Err(EthTermError::ExpectedCurryForApplicationFunctionType)?,
            }
        }
    }
}

/// function_ty.parameter_hvar(db) is None
pub(crate) fn ethereal_term_application_declarative_ty_nondependent_aux(
    db: &::salsa::Db,
    function_ty: DecCurry,
    argument_ty: RawType,
    shift: u8,
) -> EthTermResult<DecTerm> {
    debug_assert!(function_ty.parameter_hvar(db).is_none());
    match shift {
        0 => Ok(function_ty.return_ty(db)),
        shift => match argument_ty {
            RawType::Declarative(DecTerm::Curry(argument_ty)) => Ok(DecCurry::new_nondependent(
                db,
                argument_ty.toolchain(db),
                argument_ty.curry_kind(db),
                argument_ty.variance(db),
                argument_ty.parameter_ty(db),
                ethereal_term_application_declarative_ty_nondependent_aux(
                    db,
                    function_ty,
                    argument_ty.return_ty(db).into(),
                    shift - 1,
                )?,
            )
            .into()),
            _ => Err(EthTermError::ExpectedCurryForApplicationFunctionType)?,
        },
    }
}

impl EthTerm {
    fn ty_curry_parameter_count(self, db: &::salsa::Db) -> EthTermResult<u8> {
        Ok(match self.raw_ty(db)? {
            RawType::Declarative(ty) => ty.curry_parameter_count(db),
            _ => 0,
        })
    }
}

impl salsa::DisplayWithDb for EthApplication {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        self.function(db).display_fmt_with_db(f, db)?;
        f.write_str(" ")?;
        self.argument(db).display_fmt_with_db(f, db)
    }
}

impl EthApplication {
    pub(super) fn substitute(self, substitution: EthTermSubstitution, db: &::salsa::Db) -> EthTerm
    where
        Self: Copy,
    {
        let old_m = self.function(db);
        let m = old_m.substitute(substitution, db);
        let old_n = self.argument(db);
        let n = old_n.substitute(substitution, db);
        if old_m == m && old_n == n {
            return self.into();
        }
        EthApplication::new_inner(db, m, n, self.shift(db)).reduce(db)
    }
}

impl EthInstantiate for EthApplication {
    type Output = EthTerm;

    fn instantiate(
        self,
        instantiation: &EthInstantiation,
        ctx: impl IsEthTermContextRef,
        db: &::salsa::Db,
    ) -> Self::Output {
        Self::new_reduced(
            db,
            self.function(db).instantiate(instantiation, ctx, db),
            self.argument(db).instantiate(instantiation, ctx, db),
            self.shift(db),
        )
    }
}
