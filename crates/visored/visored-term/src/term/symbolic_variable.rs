use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdSymbolicVariable(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdSymbolicVariableData {
    // Add appropriate fields here
}
