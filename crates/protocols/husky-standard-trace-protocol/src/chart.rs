use husky_standard_linket_impl::var::StandardVarId;
use husky_trace_protocol::chart::{Chart, ChartDim0, ChartDim1, ChartDim2};

pub type StandardChart<R> = Chart<StandardVarId, R>;
pub type StandardChartDim0<R> = ChartDim0<StandardVarId, R>;
pub type StandardChartDim1<R> = ChartDim1<StandardVarId, R>;
pub type StandardChartDim2<R> = ChartDim2<StandardVarId, R>;
