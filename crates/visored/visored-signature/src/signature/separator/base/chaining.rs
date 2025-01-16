pub mod relation;

use self::relation::*;
use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseChainingSeparatorSignature {
    Iff,
    Relation(VdBaseRelationSignature),
}
