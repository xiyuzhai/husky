use super::{server::IsTracetime, *};
use husky_websocket_utils::imgui_client::CreationStatus;

pub fn g() {
    let x = 1;
    tracing::debug!(?x);
    tracing::info!(?x);
}

pub trait TestTraceClient: IsTracetime {
    fn test_trace_client(self);
}

impl<T> TestTraceClient for T
where
    T: IsTracetime,
{
    fn test_trace_client(self) {
        let tokio_runtime = Arc::new(tokio::runtime::Runtime::new().unwrap());
        let server_thread = std::thread::spawn(|| self.serve_traces("localhost:58888"));
        let sleep = |t| std::thread::sleep(std::time::Duration::from_millis(t));
        // wait until the server is there for sure
        let x = 1;
        tracing::debug!(?x);
        tracing::info!(?x);
        sleep(10);
        let mut client =
            TraceClient::<T::TraceProtocol, ()>::new(tokio_runtime, "ws://localhost:58888/ws", ());
        let x = 1;
        tracing::debug!(?x);
        tracing::info!(?x);
        // two updates are needed because first the connection needs to get refreshed, then client needs to get updated by receiving the init response
        sleep(1000);
        client.update();
        sleep(1000);
        client.update();
        sleep(1000);
        client.update();
        match client.connection.creation_status() {
            CreationStatus::Await(_) => todo!(),
            CreationStatus::Ok => (),
            CreationStatus::Err(_) => todo!(),
        }
        // todo!();
        client.take_view_action(TraceViewAction::FollowTrace {
            followed: TraceId::from_index(0),
        });
        // server_thread.join();
    }
}
