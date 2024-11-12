use super::*;

#[derive(Debug)]
pub struct OwnedValue(Box<dyn ImmortalDyn>);

impl std::ops::Deref for OwnedValue {
    type Target = dyn ImmortalDyn;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl PartialEq for OwnedValue {
    fn eq(&self, other: &Self) -> bool {
        // self.0 == other.0
        todo!()
    }
}

impl Eq for OwnedValue {}

impl OwnedValue {
    pub(super) fn index_owned_dyn(self, index: usize) -> ExceptedValue {
        self.0.index_owned_dyn(index)
    }

    pub(super) fn upcast_from_owned<T>(t: T) -> Self
    where
        T: Immortal,
    {
        Self(Box::<T>::new(t))
    }

    pub fn downcast_into_owned<T>(self) -> T
    where
        T: 'static,
    {
        *((self.0 as Box<dyn std::any::Any>).downcast().unwrap())
    }

    pub(super) fn downcast_as_ref<T>(&self) -> &T
    where
        T: Immortal,
    {
        unsafe {
            std::mem::transmute(
                ((&*self.0 as &dyn ImmortalDyn) as &dyn std::any::Any)
                    .downcast_ref::<T>()
                    .unwrap(),
            )
        }
    }

    pub(super) fn downcast_as_leash<T>(&self) -> &T
    where
        T: ImmortalDyn,
    {
        unsafe {
            std::mem::transmute(
                ((&*self.0 as &dyn ImmortalDyn) as &dyn std::any::Any)
                    .downcast_ref::<T>()
                    .unwrap(),
            )
        }
    }

    pub(super) fn into_inner(self) -> Box<dyn ImmortalDyn> {
        self.0
    }

    pub(super) fn as_ref(&self) -> &dyn ImmortalDyn {
        &*self.0
    }
}
