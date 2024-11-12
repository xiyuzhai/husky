use std::sync::atomic::{AtomicBool, Ordering};

pub static DEBUG_FLAG: AtomicBool = AtomicBool::new(false);

pub fn set_debug() {
    DEBUG_FLAG.store(true, Ordering::SeqCst);
}

pub fn is_debug() -> bool {
    DEBUG_FLAG.load(Ordering::SeqCst)
}
