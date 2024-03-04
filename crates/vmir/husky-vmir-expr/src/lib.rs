pub mod block;
mod builder;
pub mod destroyer;
pub mod expr;
pub mod region;
pub mod stmt;
pub mod storage;
pub mod vmir;

use builder::VmirExprBuilder;

pub(crate) trait ToVmir: Copy {
    type Output;

    fn to_vmir(self, builder: &mut VmirExprBuilder) -> Self::Output;
}