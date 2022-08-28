use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    error::CompilerError,
    r#type::{Type, TypeHash, TypeObj},
};

use std::{collections::HashSet, hash::Hash};

/// Represents a c-like struct type.
/// Limitations and warnings on its usage are similar to that in MLIR.
/// https://mlir.llvm.org/docs/Dialects/LLVM/#structure-types
///   1. Anonymous structs cannot be recursive.
///   2. Named structs are uniqued *only* by name, and may be recursive.
///      Call "set_fields" after creation to set recursive types.
struct StructType {
    name: String,
    fields: Vec<(String, Ptr<TypeObj>)>,
}

impl Verify for StructType {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

impl Stringable for StructType {
    fn to_string(&self, ctx: &Context) -> String {
        use std::cell::RefCell;
        // Ugly, but also the simplest way to avoid infinite recursion.
        // MLIR does the same: see LLVMTypeSyntax::printStructType.
        thread_local! {
            static IN_PRINTING: RefCell<HashSet<String>>  = RefCell::new(HashSet::new());
        }
        let in_printing = IN_PRINTING.with(|f| f.borrow().contains(&self.name));
        if in_printing {
            return self.name.clone();
        }
        IN_PRINTING.with(|f| f.borrow_mut().insert(self.name.clone()));
        let mut s = format!("{} {{ ", self.name);
        for field in &self.fields {
            s += [
                field.0.clone(),
                ": ".to_string(),
                field.1.deref(ctx).to_string(ctx),
                ", ".to_string(),
            ]
            .concat()
            .as_str();
        }
        s += "}";
        // Done processing this struct. Remove it from the stack.
        IN_PRINTING.with(|f| f.borrow_mut().remove(&self.name));
        s
    }
}

impl Hash for StructType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        // NOTE: Does not hash the fields due to possibility
        // of recursive types.
    }
}

impl Type for StructType {
    fn compute_hash(&self) -> TypeHash {
        TypeHash::new(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        common_traits::Stringable,
        context::Context,
        dialects::{
            builtin::types::{IntType, PointerType},
            llvm::types::StructType,
        },
        r#type::Type,
    };

    #[test]
    fn test_struct() {
        let mut ctx = Context::new();
        let int64_ptr = Type::register(IntType { width: 64 }, &mut ctx);
        // Let's build a linked list structure and verify it.
        let list_struct = Type::register(
            StructType {
                name: "LinkedList".to_string(),
                fields: vec![],
            },
            &mut ctx,
        );
        let list_ptr = Type::register(PointerType { to: list_struct }, &mut ctx);
        {
            // Modify the fields. These aren't part of what's originally built.
            let mut typeref = list_struct.deref_mut(&ctx);
            let list_ref = typeref.downcast_mut::<StructType>().unwrap();
            list_ref.fields = vec![
                ("data".to_string(), int64_ptr),
                ("next".to_string(), list_ptr),
            ];
        }
        assert!(
            list_struct
                .deref(&ctx)
                .downcast_ref::<StructType>()
                .unwrap()
                .to_string(&ctx)
                == "LinkedList { data: i64, next: LinkedList*, }"
        );
    }
}
