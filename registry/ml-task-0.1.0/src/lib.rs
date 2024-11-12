pub mod label;

use ad_hoc_devsoul_dependency::{ugly::*, *};
use husky_core::*;
use var_id::IsVarId;

pub trait IsMlTask<VarId: IsVarId> {
    type Input;

    type INPUT: __IsStaticVar<VarId>;
}
