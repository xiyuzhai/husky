use husky_item_path_interface::ItemPathIdInterface;
use husky_linket_impl::{pedestal::JointPedestal, var_id::IsVarId};
use vec_like::SmallVecPairMap;

/// the name comes from differential geometry and algebraic geometry
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum Chart<VarId: IsVarId, R> {
    Dim0(ChartDim0<VarId, R>),
    Dim1(ChartDim1<VarId, R>),
    Dim2(ChartDim2<VarId, R>),
}

pub type ChartDim0<VarId, R> = (JointPedestal<VarId>, R);
pub type ChartDim1<VarId, R> = Vec<(JointPedestal<VarId>, R)>;
pub type ChartDim2<VarId, R> = Vec<Vec<(JointPedestal<VarId>, R)>>;
