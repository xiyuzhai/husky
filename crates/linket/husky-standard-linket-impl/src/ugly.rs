pub use crate::{
    dev_eval_context::{
        dev_eval_context as __dev_eval_context, eval_eager_val_with as __eval_eager_val_with,
        eval_generic_gn_with as __eval_generic_gn_with,
        eval_ki_domain_repr_interface as __eval_ki_domain_repr_interface,
        eval_ki_repr_interface as __eval_ki_repr_interface,
        eval_ki_runtime_compterm as __eval_ki_runtime_compterm, eval_lazy_val as __eval_lazy_val,
        eval_memo_field_with as __eval_memo_field_with,
    },
    exception::{
        StandardTrackedExcepted as __TrackedExcepted,
        StandardTrackedException as __TrackedException,
    },
    pedestal::StandardPedestal as __Pedestal,
    var::StandardVarId as __VarId,
    IsGnItem as __IsGnItem, StandardKiControlFlow as __KiControlFlow,
    StandardLinketImpl as __LinketImpl, StandardVmArgumentValue as __VmArgumentValue,
    StandardVmArgumentValues as __VmArgumentValues, StandardVmControlFlow as __VmControlFlow,
};
pub use husky_item_path_interface::ugly::*;
pub use husky_ki_repr_interface::ugly::*;
pub use husky_linket_impl::ugly::*;
pub use husky_standard_value::ugly::*;

use husky_linket_impl::static_var::{StaticVarResult, StaticVarSvtable};

pub type __StaticVarResult<T> = StaticVarResult<__VarId, T>;
pub type __StaticVarSvtable = StaticVarSvtable<__VarId, __Value>;
