/// This test is in a separate file to ensure that the duplicate key error is not
/// triggered for other tests. Rust compiles each integration test file as a separate
/// crate, ensuring that other tests aren't impacted.
use pliron::{context::Context, dict_key};

dict_key!(KEY1, "test_key");
dict_key!(KEY2, "test_key");

#[test]
#[should_panic(
    expected = "Duplicate dictionary key \"test_key\" declared in tests/dict_key_duplicate.rs:6:1 and tests/dict_key_duplicate.rs:7:1"
)]
fn test_duplicate_dict_keys() {
    let _ = Context::new();
    let _ = KEY1.clone();
    let _ = KEY2.clone();
}
