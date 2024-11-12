use crate::*;
use husky_path_utils::HuskyLangDevPaths;
use husky_standard_devsoul::StandardDevsoul;
use husky_standard_trace_protocol::figure::StandardFigure;
use std::sync::Mutex;

type StandardDevRuntime = DevRuntime<StandardDevsoul>;

static RUNTIME_TEST_LOCK: Mutex<()> = Mutex::new(());

pub fn runtime_test_lock() -> std::sync::LockResult<std::sync::MutexGuard<'static, ()>> {
    RUNTIME_TEST_LOCK.lock()
}

#[test]
fn dev_runtime_works() {
    let lock = runtime_test_lock();
    let dev_paths = HuskyLangDevPaths::new();
    let dev_runtime =
        StandardDevRuntime::new(&dev_paths.examples_dir().join("mnist-classifier"), None).unwrap();
}

#[test]
fn dev_runtimes_works() {
    let lock = runtime_test_lock();
    let dev_paths = HuskyLangDevPaths::new();
    let dev_runtime =
        StandardDevRuntime::new(&dev_paths.examples_dir().join("mnist-classifier"), None).unwrap();
    std::thread::spawn(move || {
        let lock = runtime_test_lock();
        let dev_runtime =
            StandardDevRuntime::new(&dev_paths.examples_dir().join("mnist-classifier"), None)
                .unwrap();
    });
}
