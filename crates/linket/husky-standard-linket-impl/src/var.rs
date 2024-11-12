use crate::*;
use husky_linket_impl::var_id::IsVarId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum StandardVarId {
    Single(u32) = 1,
    Pair([u32; 2]),
    Triple([u32; 3]),
    Quadruple([u32; 4]),
}

#[test]
fn test_option_standard_var_id_size() {
    assert_eq!(
        std::mem::size_of::<StandardVarId>(),
        std::mem::size_of::<Option<StandardVarId>>()
    );
}

impl IsVarId for StandardVarId {
    /// removes last component
    fn generalize(self) -> Option<Self> {
        match self {
            StandardVarId::Single(_) => None,
            StandardVarId::Pair([a, _]) => Some(StandardVarId::Single(a)),
            StandardVarId::Triple([a, b, _]) => Some(StandardVarId::Pair([a, b])),
            StandardVarId::Quadruple([a, b, c, _]) => Some(StandardVarId::Triple([a, b, c])),
        }
    }

    /// append `raw_id` as last component
    #[track_caller]
    fn specialize(self, raw_id: u32) -> Self {
        match self {
            StandardVarId::Single(a) => StandardVarId::Pair([a, raw_id]),
            StandardVarId::Pair([a, b]) => StandardVarId::Triple([a, b, raw_id]),
            StandardVarId::Triple([a, b, c]) => StandardVarId::Quadruple([a, b, c, raw_id]),
            StandardVarId::Quadruple(_) => unreachable!("reached max level of specialization"), // Cannot specialize further, return self
        }
    }
}

impl StandardVarId {
    pub fn new_single(data: u32) -> Self {
        Self::Single(data)
    }

    pub fn new_pair(data: [u32; 2]) -> Self {
        Self::Pair(data)
    }

    pub fn new_triple(data: [u32; 3]) -> Self {
        Self::Triple(data)
    }

    pub fn new_quadruple(data: [u32; 4]) -> Self {
        Self::Quadruple(data)
    }
}

impl From<u32> for StandardVarId {
    fn from(data: u32) -> Self {
        StandardVarId::Single(data)
    }
}

impl Into<u32> for StandardVarId {
    fn into(self) -> u32 {
        match self {
            StandardVarId::Single(_) => todo!(),
            StandardVarId::Pair(_) | StandardVarId::Triple(_) | StandardVarId::Quadruple(_) => {
                unreachable!()
            }
        }
    }
}

impl From<usize> for StandardVarId {
    fn from(data: usize) -> Self {
        StandardVarId::Single(data.try_into().unwrap())
    }
}

impl Into<usize> for StandardVarId {
    fn into(self) -> usize {
        match self {
            StandardVarId::Single(v) => v as usize,
            StandardVarId::Pair(_) | StandardVarId::Triple(_) | StandardVarId::Quadruple(_) => {
                unreachable!()
            }
        }
    }
}

impl From<[u32; 2]> for StandardVarId {
    fn from(data: [u32; 2]) -> Self {
        StandardVarId::Pair(data)
    }
}

impl From<[u32; 3]> for StandardVarId {
    fn from(data: [u32; 3]) -> Self {
        StandardVarId::Triple(data)
    }
}

impl From<[u32; 4]> for StandardVarId {
    fn from(data: [u32; 4]) -> Self {
        StandardVarId::Quadruple(data)
    }
}

#[macro_export]
macro_rules! static_var_linket_impl {
    ($var_path: path, $item_path_id_interface: path) => {{
        static __SVTABLE: __StaticVarSvtable = __StaticVarSvtable::new::<$var_path>();
        __LinketImpl::StaticVar {
            init_item_path_id_interface: |item_path_id_interface| unsafe {
                $item_path_id_interface = Some(item_path_id_interface)
            },
            get_var_id: <$var_path as __IsStaticVar<__VarId>>::get_id,
            try_set_var_id: |id, locked| unsafe {
                <$var_path as __IsStaticVar<__VarId>>::try_set_var_id(id, locked)
                    .map(|restore| -> Box<dyn FnOnce()> { Box::new(restore) })
            },
            try_set_default_var_id: |locked| unsafe {
                <$var_path as __IsStaticVar<__VarId>>::try_set_default_var_id(locked).map(
                    |(default, restore)| -> (__VarId, Box<dyn FnOnce()>) {
                        (default, Box::new(restore))
                    },
                )
            },
            get_value: <$var_path as __IsStaticVar<__VarId>>::get_value,
            svtable: &__SVTABLE,
        }
    }};
}

#[test]
fn static_var_linket_impl_works() {
    use crate::{pedestal::StandardPedestal, ugly::*, var::StandardVarId};
    use husky_linket_impl::static_var::IsStaticVar;
    use StandardLinketImpl as __LinketImpl;

    #[allow(non_camel_case_types)]
    struct STATIC_VAR_A {}

    impl __IsStaticVar<__VarId> for STATIC_VAR_A {
        fn item_path_id_interface() -> ItemPathIdInterface {
            todo!()
        }

        fn page_var_ids_aux(locked: &[ItemPathIdInterface]) -> impl Iterator<Item = __VarId> {
            (0..10u32).map(Into::into)
        }

        fn get_id() -> __VarId {
            todo!()
        }

        fn try_set_var_id_aux(
            id: __VarId,
            locked: &[ItemPathIdInterface],
        ) -> __StaticVarResult<impl FnOnce() + 'static> {
            todo!();
            Ok(|| todo!())
        }

        type Value = Value;

        fn get_value() -> Self::Value {
            todo!()
        }

        fn default_page_start(
            figure_zone: __FigureZone,
            locked: &[ItemPathIdInterface],
        ) -> StaticVarResult<__VarId, __VarId> {
            todo!()
        }

        fn try_set_default_var_id(
            locked: &[ItemPathIdInterface],
        ) -> StaticVarResult<__VarId, (__VarId, impl FnOnce() + 'static)> {
            todo!();
            Ok((todo!(), || todo!()))
        }

        fn zones() -> &'static [husky_linket_impl::ugly::__FigureZone] {
            todo!()
        }
    }

    /// We use the same name
    thread_local! {
        pub static STATIC_VAR_A: std::cell::Cell<i32> = Default::default();
    }

    #[allow(non_upper_case_globals)]
    pub static mut STATIC_VAR_A__ITEM_PATH_ID_INTERFACE: Option<ItemPathIdInterface> = None;

    let LinketImpl::StaticVar { .. } =
        static_var_linket_impl!(STATIC_VAR_A, STATIC_VAR_A__ITEM_PATH_ID_INTERFACE)
    else {
        unreachable!()
    };
}
