pub mod source;

use crate::genki::source::GenkiReprSource;
use crate::*;
use husky_ki::genki::{GenkiOpn, GenkiRuntimeConstant};
use smallvec::SmallVec;

#[salsa::interned(constructor = new_inner)]
pub struct GenkiRepr {
    pub ki_domain_repr: GenkiDomainRepr,
    pub opn: GenkiOpn,
    #[return_ref]
    pub arguments: SmallVec<[GenkiArgumentRepr; 4]>,
    /// the source tells the code and the dependent variables that generates this val
    pub source: GenkiReprSource,
    pub caching_class: KiCachingClass,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenkiDomainRepr {
    /// everything
    Omni,
    /// those where the val repr of type bool is defined and equals true
    ConditionSatisfied(GenkiRepr),
    /// those where the val repr of type bool is defined and equals false
    ConditionNotSatisfied(GenkiRepr),
    /// those where the val repr of type ControlFlow<(), _> is defined and equals Continue(())
    ControlNotTransferred(GenkiRepr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenkiArgumentRepr {
    Simple(GenkiRepr),
    Keyed(Option<GenkiRepr>),
    Variadic(SmallVec<[GenkiRepr; 4]>),
    Branch {
        condition: Option<GenkiRepr>,
        stmts: SmallVec<[GenkiRepr; 4]>,
    },
    // `None` means no runtime constants
    RuntimeConstants(SmallVec<[GenkiRuntimeConstant; 4]>),
}
