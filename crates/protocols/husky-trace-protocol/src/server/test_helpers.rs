use super::*;
use sealed::sealed;

#[sealed]
pub trait TestTraceServer: IsTracetime {
    fn test_trace_server(self);
}

#[sealed]
impl<T> TestTraceServer for T
where
    T: IsTracetime,
{
    fn test_trace_server(self) {
        let mut _server = TraceServer::new(self);
    }
}
