//! Common utils for tests

/// Initialize the logger for tests
pub fn init_env_logger() {
    if cfg!(target_family = "wasm") {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .try_init();
    } else {
        let _ = env_logger::builder().is_test(true).try_init();
    }
}
