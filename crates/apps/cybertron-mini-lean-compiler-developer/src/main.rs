use husky_ad_hoc_protocol::AD_HOC_WEBSOCKET_ADDRESS;
use husky_devtime::*;
use husky_standard_devsoul::StandardDevsoul;
use husky_standard_trace_protocol::figure::StandardFigure;
use std::path::PathBuf;

fn main() {
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            "husky_websocket_utils=info",
        ))
        .with(tracing_subscriber::fmt::layer())
        .init();
    let path: PathBuf = "examples/cybertron-mini-lean-compiler".into();
    let devtime: Devtime<StandardDevsoul> = Devtime::new(&path, None).expect("valid");
    devtime.serve_traces(AD_HOC_WEBSOCKET_ADDRESS)
}
