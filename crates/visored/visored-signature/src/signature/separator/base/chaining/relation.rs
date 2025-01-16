pub mod comparison;
pub mod containment;

use self::{comparison::*, containment::*};
use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseRelationSignature {
    Containment(VdBaseContainmentSignature),
    Comparison(VdBaseComparisonSignature),
}
