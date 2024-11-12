use crate::LinketImplVmControlFlowThawed;
use crate::{exception::TrackedException, *};
use dev_eval_context::DevEvalContextGuard;
use husky_item_path_interface::ItemPathIdInterface;
use husky_ki_repr_interface::KiRuntimeComptermInterface;
use husky_ki_repr_interface::{KiArgumentReprInterface, KiDomainReprInterface, KiReprInterface};
use husky_value::{exception::IsException, ki_control_flow::KiControlFlow, IsValue};
use husky_value_protocol::presentation::EnumUnitValuePresenter;
use pedestal::{IsPedestal, IsPedestalFull};
use serde::Serialize;
use smallvec::SmallVec;
use static_var::{StaticVarResult, StaticVarSvtable};
use std::fmt::{self, Debug, Formatter};
use std::num::Saturating;

pub type LinketImplStaticVarResult<LinketImpl, R> =
    StaticVarResult<<<LinketImpl as IsLinketImpl>::Pedestal as IsPedestal>::VarId, R>;

pub trait IsLinketImpl: std::fmt::Debug + Eq + Send + Sync + Copy + 'static {
    type Pedestal: IsPedestalFull;
    type Value: IsValue<Exception = Self::Exception>;
    type Exception: IsException;

    fn try_set_dev_eval_context(ctx: DevEvalContext<Self>) -> Result<DevEvalContextGuard, ()>;

    fn dev_eval_context() -> DevEvalContext<Self>;

    /// assumed that pedestal has already been
    fn eval_ki(
        self,
        ki_repr_interface: KiReprInterface,
        ki_domain_repr_interface: KiDomainReprInterface,
        arguments: &[KiArgumentReprInterface],
        ctx: DevEvalContext<Self>,
    ) -> LinketImplKiControlFlow<Self>;

    fn eval_vm(
        self,
        arguments: VmArgumentValues<Self>,
        db: &dyn std::any::Any,
    ) -> LinketImplVmControlFlowThawed<Self>;

    fn enum_index_value_presenter(self) -> EnumUnitValuePresenter;

    /// applies only for static var linkage
    fn init_item_path_id_interface(self, item_path_id_interface: ItemPathIdInterface);
    /// applies only for static var linkage
    fn static_var_id(self) -> <Self::Pedestal as IsPedestal>::VarId;
    fn with_var_id<R>(
        self,
        var_id: <Self::Pedestal as IsPedestal>::VarId,
        locked: &[ItemPathIdInterface],
        f: impl FnOnce() -> R,
    ) -> LinketImplStaticVarResult<Self, R>;
    fn with_default_var_id<R>(
        self,
        locked: &[ItemPathIdInterface],
        f: impl FnOnce(<Self::Pedestal as IsPedestal>::VarId) -> R,
    ) -> LinketImplStaticVarResult<Self, R>;
    fn static_var_svtable(
        self,
    ) -> &'static StaticVarSvtable<<Self::Pedestal as IsPedestal>::VarId, Self::Value>;
}

pub type LinketImplKiControlFlow<LinketImpl, C = <LinketImpl as IsLinketImpl>::Value> =
    KiControlFlow<C, <LinketImpl as IsLinketImpl>::Value, LinketImplTrackedException<LinketImpl>>;
pub type LinketImplVmControlFlow<LinketImpl, C = LinketImplThawedValue<LinketImpl>> =
    VmControlFlow<C, LinketImplThawedValue<LinketImpl>, LinketImplTrackedException<LinketImpl>>;

pub type LinketImplTrackedException<LinketImpl> = TrackedException<
    <LinketImpl as IsLinketImpl>::Exception,
    <LinketImpl as IsLinketImpl>::Pedestal,
>;

pub type LinketImplThawedValue<LinketImpl> =
    <<LinketImpl as IsLinketImpl>::Value as IsValue>::ThawedValue;
pub type LinketImplFrozenValue<LinketImpl> =
    <<LinketImpl as IsLinketImpl>::Value as IsValue>::FrozenValue;
pub type LinketImplSlushValue<LinketImpl> =
    <<LinketImpl as IsLinketImpl>::Value as IsValue>::SlushValue;
pub type LinketImplTrackedExceptedValue<LinketImpl> =
    Result<<LinketImpl as IsLinketImpl>::Value, LinketImplTrackedException<LinketImpl>>;

pub type LinketImplTrackedExcepted<LinketImpl, T> =
    Result<T, LinketImplTrackedException<LinketImpl>>;

pub enum VmArgumentValue<'comptime, LinketImpl: IsLinketImpl> {
    Simple(LinketImplThawedValue<LinketImpl>),
    Keyed(Option<LinketImplThawedValue<LinketImpl>>),
    Variadic(Vec<LinketImplThawedValue<LinketImpl>>),
    RuntimeConstants(&'comptime [KiRuntimeComptermInterface]),
}

pub type VmArgumentValues<'comptime, LinketImpl> =
    SmallVec<[VmArgumentValue<'comptime, LinketImpl>; 4]>;

impl<'comptime, LinketImpl: IsLinketImpl + Debug> Debug for VmArgumentValue<'comptime, LinketImpl> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VmArgumentValue::Simple(value) => f.debug_tuple("Simple").field(value).finish(),
            VmArgumentValue::Keyed(value) => f.debug_tuple("Keyed").field(value).finish(),
            VmArgumentValue::Variadic(values) => f.debug_tuple("Variadic").field(values).finish(),
            VmArgumentValue::RuntimeConstants(values) => {
                f.debug_tuple("RuntimeConstants").field(values).finish()
            }
        }
    }
}
