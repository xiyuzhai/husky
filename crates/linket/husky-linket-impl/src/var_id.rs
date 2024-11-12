pub mod virtual_var_id;

use crate::*;
use serde::{Deserialize, Serialize};

/// corresponds to Id in `salsa`
pub trait IsVarId: std::fmt::Debug + Copy + Eq + std::hash::Hash + Send + Sync + 'static {
    /// removes last component
    fn generalize(self) -> Option<Self>;
    /// append `raw_id` as last component
    fn specialize(self, raw_id: u32) -> Self;
}

pub trait IsVarIdFull: IsVarId + Serialize + for<'a> Deserialize<'a> {}

impl<VarId> IsVarIdFull for VarId where VarId: IsVarId + Serialize + for<'a> Deserialize<'a> {}
