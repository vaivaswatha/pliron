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
///   1. Anonymous (aka unnamed) structs cannot be recursive.
///   2. Named structs are uniqued *only* by name, and may be recursive.
///      Call "set_fields" after creation to set recursive types.
///   3. LLVM calls anonymous structs as literal structs and
///      named structs as identified structs.
pub struct StructType {
    name: Option<String>,
    fields: Vec<(String, Ptr<TypeObj>)>,
    finalized: bool,
}

impl StructType {
    /// Create a new named StructType.
    /// If fields is None, it indicates an opaque (i.e., not finalized) struct.
    /// Opaque structs must be finalized for verify() to succeed.
    /// Opaque structs are an intermediary in creating recursive types.
    pub fn create_named(
        ctx: &mut Context,
        name: String,
        fields: Option<Vec<(String, Ptr<TypeObj>)>>,
    ) -> Ptr<TypeObj> {
        let self_ptr = Type::register(
            StructType {
                name: Some(name.clone()),
                fields: fields.clone().unwrap_or_default(),
                finalized: fields.is_some(),
            },
            ctx,
        );
        // Verify that we created a new or equivalent existing type.
        let self_ref = self_ptr.deref(ctx);
        let self_ref = self_ref.downcast_ref::<StructType>().unwrap();
        assert!(self_ref.name.as_ref().unwrap() == &name);
        assert!(
            self_ref.finalized == fields.is_some(),
            "Struct already exists, or is being finalized via new creation"
        );
        if let Some(fields) = fields {
            assert!(
                self_ref.fields == fields,
                "Struct {} already exists and is different",
                name
            );
        };
        self_ptr
    }

    /// Create a new unnamed (anonymous) struct.
    /// These are finalized upon creation, and uniqued based on the fields.
    pub fn create_unnamed(ctx: &mut Context, fields: Vec<(String, Ptr<TypeObj>)>) -> Ptr<TypeObj> {
        Type::register(
            StructType {
                name: None,
                fields,
                finalized: true,
            },
            ctx,
        )
    }

    /// Finalize this structure. It is an error to call if already finalized.
    pub fn finalize(&mut self, fields: Vec<(String, Ptr<TypeObj>)>) {
        assert!(
            !self.finalized,
            "Attempt to finalize an already finalized struct"
        );
        self.fields = fields;
        self.finalized = true;
    }

    /// If a named struct already exists, get a pointer to it.
    /// Note that named structs are uniqued only on the name.
    pub fn get_existing_named_struct(ctx: &Context, name: String) -> Option<Ptr<TypeObj>> {
        let hash = StructType {
            name: Some(name),
            fields: vec![],
            finalized: false,
        }
        .compute_hash();
        ctx.typehash_typeptr_map.get(&hash).cloned()
    }
}

impl Verify for StructType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        if !self.finalized {
            return Err(CompilerError::VerificationError {
                msg: "Struct not finalized".to_string(),
            });
        }
        Ok(())
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
        let mut s;
        if let Some(name) = &self.name {
            let in_printing = IN_PRINTING.with(|f| f.borrow().contains(name));
            if in_printing {
                return name.clone();
            }
            IN_PRINTING.with(|f| f.borrow_mut().insert(name.clone()));
            s = format!("{} {{ ", name);
        } else {
            s = "{{ ".to_string();
        }

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
        if let Some(name) = &self.name {
            IN_PRINTING.with(|f| f.borrow_mut().remove(name));
        }
        s
    }
}

impl Hash for StructType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.name {
            Some(name) => name.hash(state),
            None => self.fields.iter().for_each(|(name, ty)| {
                name.hash(state);
                ty.hash(state);
            }),
        }
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

        // Create an opaque struct since we want a recursive type.
        let list_struct = StructType::create_named(&mut ctx, "LinkedList".to_string(), None);
        let list_struct_ptr = PointerType::create(&mut ctx, list_struct);
        let fields = vec![
            ("data".to_string(), int64_ptr),
            ("next".to_string(), list_struct_ptr),
        ];
        // Finalize the type now.
        list_struct
            .deref_mut(&mut ctx)
            .downcast_mut::<StructType>()
            .unwrap()
            .finalize(fields);

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
