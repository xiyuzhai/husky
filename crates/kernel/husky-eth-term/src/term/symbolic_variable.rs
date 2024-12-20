mod index;
mod set;

pub use self::index::*;

use super::*;
use crate::fmt::symbol_name;
use template_var_class::TemplateVariableClass;
use thiserror::Error;

#[salsa::interned(constructor = pub new_inner, override_debug)]
pub struct EthSymbolicVariable {
    pub toolchain: Toolchain,
    pub ty: EthTerm,
    /// this is the index for all symbols with the same type
    /// so that we have better cache hits
    /// todo: improve this by adding TypeFamily
    pub index: EthTermSymbolicVariableIndex,
}

#[test]
fn term_symbol_size_works() {
    assert_eq!(
        std::mem::size_of::<EthSymbolicVariable>(),
        std::mem::size_of::<u32>()
    );
}

impl EthSymbolicVariable {
    #[inline(always)]
    pub fn from_dec(
        db: &::salsa::Db,
        dec_symbolic_variable: DecSymbolicVariable,
    ) -> EthTermResult<Self> {
        let ty = dec_symbolic_variable.ty(db)?;
        let ty = EthTerm::ty_from_dec(db, ty)?;
        Ok(Self::new_inner(
            db,
            dec_symbolic_variable.toolchain(db),
            ty,
            EthTermSymbolicVariableIndex::from_dec(dec_symbolic_variable.index(db)),
        ))
    }
}

impl EthSymbolicVariable {
    pub fn class(self, db: &::salsa::Db) -> Option<TemplateVariableClass> {
        match self.index(db).inner() {
            EthTermVariableIndexImpl::ExplicitLifetime { attrs, .. } => Some(attrs.class),
            EthTermVariableIndexImpl::ExplicitPlace {
                attrs,
                variance,
                disambiguator,
            } => Some(attrs.class),
            EthTermVariableIndexImpl::Type {
                attrs,
                variance,
                disambiguator,
            } => Some(attrs.class),
            EthTermVariableIndexImpl::Prop { disambiguator } => None,
            EthTermVariableIndexImpl::ConstPathLeading {
                attrs,
                disambiguator,
                ty_path,
            } => Some(attrs.class),
            EthTermVariableIndexImpl::ConstOther {
                attrs,
                disambiguator,
            } => Some(attrs.class),
            EthTermVariableIndexImpl::EphemPathLeading {
                disambiguator,
                ty_path,
            } => None,
            EthTermVariableIndexImpl::EphemOther { disambiguator } => None,
            EthTermVariableIndexImpl::SelfType => None,
            EthTermVariableIndexImpl::SelfValue => None,
            EthTermVariableIndexImpl::SelfLifetime => None,
            EthTermVariableIndexImpl::SelfPlace => None,
        }
    }
}

#[derive(Debug, Error, PartialEq, Eq, Clone, Copy, Hash)]
pub enum TermSymbolTypeErrorKind {
    #[error("signature term error")]
    SignatureTermError,
    #[error("sketch term error")]
    SketchTermError,
}
pub type TermSymbolTypeResult<T> = Result<T, TermSymbolTypeErrorKind>;

impl salsa::DebugWithDb for EthSymbolicVariable {
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &salsa::Db,
    ) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "EthSymbolicVariable(`{}`, `{}`)",
            self.display(db),
            match self.class(db) {
                Some(class) => match class {
                    TemplateVariableClass::Mono => "mono",
                    TemplateVariableClass::Poly => "poly",
                    TemplateVariableClass::Phan => "phan",
                },
                None => "nil",
            }
        ))
    }
}

impl salsa::DisplayWithDb for EthSymbolicVariable {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        symbol_name(*self, db).display_fmt_with_db(f, db)
    }
}

impl EthInstantiate for EthSymbolicVariable {
    type Output = EthTerm;

    fn instantiate(
        self,
        instantiation: &EthInstantiation,
        ctx: impl IsEthTermContextRef,
        db: &::salsa::Db,
    ) -> Self::Output {
        // it's assumed that all symbols will be replaced by its map
        // otherwise it's illegal
        instantiation.symbol_instantiation(self)
    }
}
