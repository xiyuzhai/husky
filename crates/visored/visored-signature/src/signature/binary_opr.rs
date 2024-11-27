pub mod base;
pub mod composite;

use self::{base::*, composite::*};
use super::*;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdBinaryOprSignature {
    Base(VdBaseBinaryOprSignature),
}
