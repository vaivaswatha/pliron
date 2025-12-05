//! Safe(r) wrappers around llvm_sys::lljit
//!
//! ### Example
//!```
//! use pliron_llvm::llvm_sys::target::initialize_native;
//! use pliron_llvm::llvm_sys::core::{LLVMContext, LLVMModule, LLVMMemoryBuffer};
//! use pliron_llvm::llvm_sys::lljit::LLVMLLJIT;
//! fn main() -> Result<(), String> {
//!     initialize_native()?;
//!
//!     let context = LLVMContext::default();
//!     let ir = r#"
//!         define i32 @add(i32 %a, i32 %b) {
//!             %sum = add i32 %a, %b
//!             ret i32 %sum
//!         }"#;
//!     let ir_mb = LLVMMemoryBuffer::from_str(ir, "test_buffer");
//!     let module = LLVMModule::from_ir_in_memory_buffer(&context, ir_mb)?;
//!
//!     let jit = LLVMLLJIT::new_with_default_builder()?;
//!     jit.add_module(module)?;
//!     let symbol_addr = jit.lookup_symbol("add")?;
//!     assert!(symbol_addr != 0);
//!
//!     let adder = unsafe { std::mem::transmute::<u64, fn(i32, i32) -> i32>(symbol_addr) };
//!     assert_eq!(adder(2, 3), 5);
//!     Ok(())
//! }
//! ```

use std::{mem::MaybeUninit, ptr};

use llvm_sys::orc2::{
    LLVMOrcCreateNewThreadSafeContext, LLVMOrcCreateNewThreadSafeModule,
    LLVMOrcDisposeThreadSafeContext, LLVMOrcDisposeThreadSafeModule, lljit,
};

use crate::llvm_sys::{
    core::{LLVMModule, handle_err},
    cstr_to_string, to_c_str,
};

pub struct LLVMLLJIT(lljit::LLVMOrcLLJITRef);

impl LLVMLLJIT {
    /// Create a new LLJIT instance with default settings.
    pub fn new_with_default_builder() -> Result<Self, String> {
        unsafe {
            let mut jit = MaybeUninit::uninit();
            let err = lljit::LLVMOrcCreateLLJIT(jit.as_mut_ptr(), ptr::null_mut());
            handle_err(err)?;
            Ok(LLVMLLJIT(jit.assume_init()))
        }
    }

    /// Add an [LLVMModule] to the JIT's main JITDylib, in its own thread-safe context.
    pub fn add_module(&self, module: LLVMModule) -> Result<(), String> {
        unsafe {
            let tsctx = LLVMOrcCreateNewThreadSafeContext();
            let tsm = LLVMOrcCreateNewThreadSafeModule(module.inner_ref(), tsctx);
            let main_jd = lljit::LLVMOrcLLJITGetMainJITDylib(self.0);
            let err = lljit::LLVMOrcLLJITAddLLVMIRModule(self.0, main_jd, tsm);
            // The underlying LLVMContext will be kept alive by our ThreadSafeModule
            // (See OrcV2CBindingsBasicUsage.c)
            LLVMOrcDisposeThreadSafeContext(tsctx);
            // Ownership of the module has been transferred to the JIT
            std::mem::forget(module);
            handle_err(err).inspect_err(|_| {
                // Dispose of the ThreadSafeModule on error
                LLVMOrcDisposeThreadSafeModule(tsm);
            })
        }
    }

    /// Lookup a symbol in the JIT.
    pub fn lookup_symbol(&self, name: &str) -> Result<u64, String> {
        unsafe {
            let mut addr = MaybeUninit::uninit();
            let err = lljit::LLVMOrcLLJITLookup(self.0, addr.as_mut_ptr(), to_c_str(name).as_ptr());
            handle_err(err)?;
            Ok(addr.assume_init())
        }
    }

    /// Get the target triple string for this JIT instance.
    pub fn get_triple_string(&self) -> String {
        unsafe {
            let triple_ptr = lljit::LLVMOrcLLJITGetTripleString(self.0);
            cstr_to_string(triple_ptr).unwrap()
        }
    }
}

impl Drop for LLVMLLJIT {
    fn drop(&mut self) {
        unsafe {
            let err = lljit::LLVMOrcDisposeLLJIT(self.0);
            if let Err(err) = handle_err(err) {
                panic!("Error disposing LLJIT: {}", err);
            }
        }
    }
}
