//! Common utils for tests

/// Initialize the logger for tests
pub fn init_env_logger() {
  let _ = env_logger::builder().is_test(true).try_init();
}
