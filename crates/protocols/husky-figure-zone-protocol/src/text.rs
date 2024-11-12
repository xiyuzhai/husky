use super::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use shifted_unsigned_int::ShiftedU32;

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum FigureTextKey<VarId> {
    Unit,
    VarId(VarId),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum FigureText {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct FigureTextId(ShiftedU32);

impl Serialize for FigureTextId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u32(self.0.into())
    }
}

impl<'de> Deserialize<'de> for FigureTextId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = usize::deserialize(deserializer)?;
        Ok(FigureTextId(ShiftedU32::new(value as u32)))
    }
}

#[derive(Default)]
pub struct FigureTextArena {
    data: Vec<FigureText>,
}

impl FigureTextArena {
    pub fn alloc(&mut self, text: FigureText) -> FigureTextId {
        let id = FigureTextId(ShiftedU32::new(self.data.len() as u32));
        self.data.push(text);
        id
    }
}
