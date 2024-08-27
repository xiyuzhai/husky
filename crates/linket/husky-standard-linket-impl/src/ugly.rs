pub use crate::{
    exception::{
        StandardTrackedExcepted as __TrackedExcepted,
        StandardTrackedException as __TrackedException,
    },
    pedestal::StandardPedestal as __Pedestal,
    static_var::StandardStaticVarId as __StaticVarId,
    IsGnItem as __IsGnItem, StandardKiControlFlow as __KiControlFlow,
    StandardLinketImpl as __LinketImpl,
};
pub use husky_ki_repr_interface::ugly::*;
use husky_linket_impl::static_var::StaticVarResult;
pub use husky_linket_impl::ugly::*;
pub use husky_standard_value::ugly::*;

pub type __StaticVarResult<T> = StaticVarResult<__StaticVarId, T>;