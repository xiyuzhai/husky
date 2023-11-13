use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::debug_with_db(db = HirTypeDb)]
pub struct HirRitchieVariadicParameter {
    contract: Contract,
    ty: HirType,
}