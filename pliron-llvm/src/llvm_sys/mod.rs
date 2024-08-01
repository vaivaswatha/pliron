//! Safe wrappers around the llvm_sys crate.
//! The wrappers provide safety by asserting that the concrete C++
//! types of arguments match the expected C++ type.
//! For example,
//! 1. `core::llvm_add_incoming(phi_node: LLVMValueRef, ...)`
//!    checks that `phi_node` is indeed a C++ `PHINode`.
//! 2. `core::llvm_count_param_types(ty: LLVMTypeRef)`
//!    checks that `ty` is a function type.
//!
//! This ensures that there are no undefined behavior / invalid memory accesses.
//! We do not check for invalid IR that is caught by the verifier.
//! As a general guideline, ensure that the C-Types (which are C++ base classes)
//! match the C++ derived class expected by the callee, via assertions.
//! (such as the PHINode: LLVMValueRef) example above.
//! Type-checking the LLVM-IR itself is left to the verifier, with exceptions.
//! Exceptions include constraints on `LLVMTypeRef`, for example `ArrayType`'s
//! element must satisfy `llvm_is_valid_array_element_type`. This isn't verified
//! by the verifier.

pub mod core;

use llvm_sys::prelude::LLVMBool;
use std::{
    borrow::Cow,
    ffi::{CStr, CString},
    mem::MaybeUninit,
};

/// Create an uninitialized vector with given length.
unsafe fn uninitialized_vec<T>(len: usize) -> MaybeUninit<Vec<T>> {
    let mut v = MaybeUninit::new(Vec::with_capacity(len));
    unsafe {
        v.assume_init_mut().set_len(len);
    }
    v
}

/// Convert a null-terminated, possibly null, C string to [String].
fn cstr_to_string(ptr: *const ::core::ffi::c_char) -> Option<String> {
    if ptr.is_null() {
        return None;
    }
    Some(
        unsafe { CStr::from_ptr(ptr) }
            .to_str()
            .expect("CStr not UTF-8")
            .to_owned(),
    )
}

/// Convert a non-null-terminated, possibly null C string to [String]
fn sized_cstr_to_string(ptr: *const ::core::ffi::c_char, len: usize) -> Option<String> {
    if ptr.is_null() {
        return None;
    }

    let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len) };
    Some(
        std::str::from_utf8(slice)
            .expect("CStr not UTF-8")
            .to_owned(),
    )
}

/// Convert a value to `bool`
trait ToBool {
    fn to_bool(&self) -> bool;
}

impl ToBool for LLVMBool {
    fn to_bool(&self) -> bool {
        *self != 0
    }
}

/// This function takes in a Rust string and either:
///
/// A) Finds a terminating null byte in the Rust string and can reference it directly like a C string.
///
/// B) Finds no null byte and allocates a new C string based on the input Rust string.
///
/// This function and its test are taken from the [inkwell](https://github.com/thedan64/inkwell/) project
fn to_c_str(mut s: &str) -> Cow<'_, CStr> {
    if s.is_empty() {
        s = "\0";
    }

    // Start from the end of the string as it's the most likely place to find a null byte
    if !s.chars().rev().any(|ch| ch == '\0') {
        return Cow::from(CString::new(s).expect("unreachable since null bytes are checked"));
    }

    unsafe { Cow::from(CStr::from_ptr(s.as_ptr() as *const _)) }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::borrow::Cow;

    use crate::llvm_sys::to_c_str;

    #[test]
    fn test_to_c_str() {
        assert!(matches!(to_c_str("my string"), Cow::Owned(_)));
        assert!(matches!(to_c_str("my string\0"), Cow::Borrowed(_)));
    }
}
