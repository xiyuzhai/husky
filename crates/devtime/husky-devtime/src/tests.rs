use crate::*;
use husky_path_utils::HuskyLangDevPaths;
use husky_standard_devsoul::StandardDevsoul;
use husky_standard_trace_protocol::figure::StandardFigure;
use husky_trace_protocol::{
    client::test_helpers::TestTraceClient,
    server::{test_helpers::TestTraceServer, TraceServer},
};
use tracing_test::traced_test;

// it looks ugly, lol
type StandardDevtime = Devtime<StandardDevsoul>;

#[test]
#[ignore]
fn devtime_trace_server_works() {
    let dev_paths = HuskyLangDevPaths::new();
    let devtime =
        StandardDevtime::new(&dev_paths.examples_dir().join("mnist-classifier"), None).unwrap();
    devtime.test_trace_server();
}

#[traced_test]
#[test]
#[ignore]
fn devtime_trace_client_works() {
    let dev_paths = HuskyLangDevPaths::new();
    let devtime =
        StandardDevtime::new(&dev_paths.examples_dir().join("mnist-classifier"), None).unwrap();
    devtime.test_trace_client();
}
