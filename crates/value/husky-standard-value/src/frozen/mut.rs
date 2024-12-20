pub mod slice;

use super::*;
use crate::thawed::Thawed;
use thawed::r#mut::ThawedMut;

#[derive(Debug)]
pub struct FrozenMut<T>(Box<T>)
where
    T: Frozen;

impl<T> FrozenMut<T>
where
    T: Frozen,
{
    pub(crate) unsafe fn new(t: *mut T) -> Self {
        todo!()
        // Self(Box::new(<T as Thawed>::freeze(&*t)))
    }
}

impl<T> Clone for FrozenMut<T>
where
    T: Frozen,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Frozen for FrozenMut<T>
where
    T: Frozen,
{
    type Thawed = ThawedMut<T::Thawed>;

    type Slush = Box<T::Slush>;

    fn thaw(&self) -> (Option<Self::Slush>, Self::Thawed) {
        todo!()
    }

    fn serialize_to_value(&self) -> serde_json::Value {
        todo!()
    }

    fn visualize_or_void(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual {
        todo!()
    }
}
