use husky_item_path_interface::ItemPathIdInterface;
use husky_ki_repr_interface::{KiArgumentReprInterface, KiDomainReprInterface, KiReprInterface};
use husky_linket::linket::{Linket, LinketData};
use husky_linket_impl::{dev_eval_context::DevEvalContext, linket_impl::IsLinketImpl};
use husky_linket_impl::{linket_impl::LinketImplStaticVarResult, pedestal::IsPedestal};
use husky_linket_impl::{
    linket_impl::VmArgumentValues, pedestal::virtual_pedestal::VirtualPedestal,
};
use husky_linket_impl::{
    linket_impl::{LinketImplKiControlFlow, VmArgumentValue},
    LinketImplVmControlFlowThawed,
};
use husky_value::vm_control_flow::VmControlFlow;
use husky_value_protocol::presentation::EnumUnitValuePresenter;
use husky_virtual_value::{exception::Exception, value::Value};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct VirtualLinketImpl(Linket);

impl std::ops::Deref for VirtualLinketImpl {
    type Target = Linket;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Linket> for VirtualLinketImpl {
    fn from(linket: Linket) -> Self {
        Self(linket)
    }
}

impl IsLinketImpl for VirtualLinketImpl {
    type Pedestal = VirtualPedestal;

    type Value = Value;

    type Exception = Exception;

    fn dev_eval_context() -> DevEvalContext<Self> {
        todo!()
    }

    fn eval_ki(
        self,
        ki_repr_interface: KiReprInterface,
        ki_domain_repr_interface: KiDomainReprInterface,
        arguments: &[KiArgumentReprInterface],
        ctx: DevEvalContext<Self>,
    ) -> LinketImplKiControlFlow<Self> {
        todo!()
    }

    fn eval_vm(
        self,
        mut arguments: VmArgumentValues<Self>,
        db: &dyn std::any::Any,
    ) -> LinketImplVmControlFlowThawed<Self> {
        use VmControlFlow::Continue;

        let db: &::salsa::Db = db.downcast_ref().unwrap();
        match self.data(db) {
            LinketData::MajorRitchie {
                path,
                instantiation,
            } => todo!(),
            LinketData::MajorStaticVar {
                path,
                instantiation,
            } => todo!(),
            LinketData::MajorVal {
                path,
                instantiation,
            } => todo!(),
            LinketData::Memo {
                path,
                instantiation,
            } => todo!(),
            LinketData::MethodRitchie {
                path,
                instantiation,
            } => todo!(),
            LinketData::AssocRitchie {
                path,
                instantiation,
            } => todo!(),
            LinketData::UnveilAssocRitchie {
                path,
                instantiation,
            } => todo!(),
            LinketData::StructConstructor {
                path,
                instantiation,
            } => todo!(),
            LinketData::StructDestructor { self_ty } => todo!(),
            LinketData::EnumVariantConstructor {
                self_ty,
                path,
                instantiation,
            } => todo!(),
            LinketData::EnumVariantDiscriminator {
                self_ty,
                path,
                instantiation,
            } => todo!(),
            LinketData::EnumVariantDestructor {
                self_ty,
                path,
                instantiation,
            } => todo!(),
            LinketData::StructField {
                self_ty,
                field,
                field_ty_leash_class,
            } => todo!(),
            LinketData::EnumVariantField {
                path,
                instantiation,
                field_ty_leash_class,
                field,
            } => todo!(),
            LinketData::Index => todo!(),
            LinketData::VecConstructor { element_ty } => {
                let VmArgumentValue::Variadic(elements) = arguments.pop().unwrap() else {
                    unreachable!()
                };
                Continue(Value::Vec(elements))
            }
            LinketData::TypeDefault { ty } => todo!(),
            LinketData::EnumUnitToJsonValue { ty_path } => todo!(),
        }
    }

    fn enum_index_value_presenter(self) -> EnumUnitValuePresenter {
        todo!()
    }

    fn init_item_path_id_interface(self, item_path_id_interface: ItemPathIdInterface) {
        ()
    }

    fn static_var_id(self) -> <Self::Pedestal as IsPedestal>::VarId {
        todo!()
    }

    fn with_var_id<R>(
        self,
        static_var_id: <Self::Pedestal as IsPedestal>::VarId,
        locked: &[ItemPathIdInterface],
        f: impl FnOnce() -> R,
    ) -> LinketImplStaticVarResult<Self, R> {
        todo!()
    }

    fn with_default_var_id<R>(
        self,
        locked: &[ItemPathIdInterface],
        f: impl FnOnce(<Self::Pedestal as IsPedestal>::VarId) -> R,
    ) -> LinketImplStaticVarResult<Self, R> {
        todo!()
    }

    fn try_set_dev_eval_context(
        ctx: DevEvalContext<Self>,
    ) -> Result<husky_linket_impl::dev_eval_context::DevEvalContextGuard, ()> {
        todo!()
    }

    fn static_var_svtable(
        self,
    ) -> &'static husky_linket_impl::static_var::StaticVarSvtable<
        <Self::Pedestal as IsPedestal>::VarId,
        Self::Value,
    > {
        todo!()
    }
}
