use self::view::action::TraceViewActionBuffer;
use crate::*;
use anchor::Anchor;
use husky_item_path_interface::ItemPathIdInterface;
use husky_linket_impl::{pedestal::IsPedestal, pedestal::IsPedestalFull, var_id::IsVarId};
use ui::ui::IsUi;
use windlass::Windlass;

pub trait IsCaryatid:
    std::fmt::Debug
    + Default
    + Clone
    + Eq
    + Send
    + Sync
    + std::ops::Index<ItemPathIdInterface, Output = Windlass<<Self::Pedestal as IsPedestal>::VarId>>
    + 'static
{
    type Pedestal: IsPedestalFull;

    type UiBuffer: IsCaryatidUiBuffer<Caryatid = Self>;

    fn pedestal(&self, var_deps: &[ItemPathIdInterface]) -> Option<Self::Pedestal>;
    #[deprecated]
    fn has_var_deps(&self, var_deps: &[ItemPathIdInterface]) -> bool;
    #[deprecated]
    fn has_var_dep(&self, var_dep: ItemPathIdInterface) -> bool;
    fn windlasses(
        &self,
    ) -> &[(
        ItemPathIdInterface,
        Windlass<<Self::Pedestal as IsPedestal>::VarId>,
    )];
    /// # Panic
    ///
    /// if not new
    fn add_new(
        &mut self,
        item_path_id_interface: ItemPathIdInterface,
        windlass: Windlass<<Self::Pedestal as IsPedestal>::VarId>,
    );
}

pub trait IsCaryatidUiBuffer: Default {
    type Caryatid: IsCaryatid;

    fn show_var_id_edit<TraceProtocol>(
        &mut self,
        item_path_id_interface: ItemPathIdInterface,
        var_id: Option<<<Self::Caryatid as IsCaryatid>::Pedestal as IsPedestal>::VarId>,
        trace_synchrotron: &TraceSynchrotron<TraceProtocol>,
    ) where
        TraceProtocol: IsTraceProtocol<
            Pedestal = <Self::Caryatid as IsCaryatid>::Pedestal,
            Caryatid = Self::Caryatid,
        >;

    fn var_id_edit(&mut self, item_path_id_interface: ItemPathIdInterface) -> Option<&mut String>;
}

pub trait IsCaryatidFull: IsCaryatid + Serialize + for<'a> Deserialize<'a> {}

impl<T> IsCaryatidFull for T where T: IsCaryatid + Serialize + for<'a> Deserialize<'a> {}

pub trait CaryatidUi<Ui: IsUi>: IsCaryatidFull {
    fn caryatid_ui<TraceProtocol>(
        &self,
        trace_synchrotron: &TraceSynchrotron<TraceProtocol>,
        ui: &mut Ui,
        caryatid_buffer: &mut Self::UiBuffer,
        action_buffer: &mut TraceViewActionBuffer<TraceProtocol>,
    ) where
        TraceProtocol: IsTraceProtocol<Pedestal = Self::Pedestal, Caryatid = Self>;
}

pub type TraceCaryatidUiBuffer<TraceProtocol> =
    <<TraceProtocol as IsTraceProtocol>::Caryatid as IsCaryatid>::UiBuffer;
