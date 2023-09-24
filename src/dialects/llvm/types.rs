use combine::{easy, token, ParseResult, Parser};

use crate::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::CompilerError,
    impl_type,
    parsable::{spaced, Parsable, StateStream},
    printable::{self, Printable},
    r#type::{type_parser, Type, TypeObj},
    storage_uniquer::TypeValueHash,
};

use std::hash::Hash;

/// Represents a c-like struct type.
/// Limitations and warnings on its usage are similar to that in MLIR.
/// `<https://mlir.llvm.org/docs/Dialects/LLVM/#structure-types>`
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
impl_type!(StructType, "struct", "llvm");

impl StructType {
    /// Create a new named StructType.
    /// If fields is None, it indicates an opaque (i.e., not finalized) struct.
    /// Opaque structs must be finalized for verify() to succeed.
    /// Opaque structs are an intermediary in creating recursive types.
    pub fn create_named(
        ctx: &mut Context,
        name: &str,
        fields: Option<Vec<(String, Ptr<TypeObj>)>>,
    ) -> Ptr<TypeObj> {
        let self_ptr = Type::register_instance(
            StructType {
                name: Some(name.to_string()),
                fields: fields.clone().unwrap_or_default(),
                finalized: fields.is_some(),
            },
            ctx,
        );
        // Verify that we created a new or equivalent existing type.
        let self_ref = self_ptr.deref(ctx);
        let self_ref = self_ref.downcast_ref::<StructType>().unwrap();
        assert!(self_ref.name.as_ref().unwrap() == name);
        assert!(
            self_ref.finalized == fields.is_some(),
            "Struct already exists, or is being finalized via new creation"
        );
        if let Some(fields) = fields {
            assert!(
                self_ref.fields == fields,
                "Struct {name} already exists and is different"
            );
        };
        self_ptr
    }

    /// Get or create a new unnamed (anonymous) struct.
    /// These are finalized upon creation, and uniqued based on the fields.
    pub fn get_unnamed(ctx: &mut Context, fields: Vec<(String, Ptr<TypeObj>)>) -> Ptr<TypeObj> {
        Type::register_instance(
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
    pub fn get_existing_named(ctx: &Context, name: &str) -> Option<Ptr<TypeObj>> {
        Type::get_instance(
            StructType {
                name: Some(name.to_string()),
                fields: vec![],
                finalized: false,
            },
            ctx,
        )
    }

    /// Get, if it already exists, a [Ptr] to an unnamed struct.
    pub fn get_existing_unnamed(
        ctx: &Context,
        fields: Vec<(String, Ptr<TypeObj>)>,
    ) -> Option<Ptr<TypeObj>> {
        Type::get_instance(
            StructType {
                name: None,
                fields,
                finalized: true,
            },
            ctx,
        )
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

impl Printable for StructType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{} <", Self::get_type_id_static().disp(ctx))?;
        use std::cell::RefCell;
        // Ugly, but also the simplest way to avoid infinite recursion.
        // MLIR does the same: see LLVMTypeSyntax::printStructType.
        thread_local! {
            // We use a vec instead of a HashMap hoping that this isn't
            // going to be large, in which case vec would be faster.
            static IN_PRINTING: RefCell<Vec<String>>  = RefCell::new(vec![]);
        }
        let mut s;
        if let Some(name) = &self.name {
            let in_printing = IN_PRINTING.with(|f| f.borrow().contains(name));
            if in_printing {
                return write!(f, "{}>", name.clone());
            }
            IN_PRINTING.with(|f| f.borrow_mut().push(name.clone()));
            s = format!("{name} {{ ");
        } else {
            s = "{{ ".to_string();
        }

        for field in &self.fields {
            s += [
                field.0.clone(),
                ": ".to_string(),
                field.1.deref(ctx).disp(ctx).to_string(),
                ", ".to_string(),
            ]
            .concat()
            .as_str();
        }
        s += "}";
        // Done processing this struct. Remove it from the stack.
        if let Some(name) = &self.name {
            debug_assert!(IN_PRINTING.with(|f| f.borrow().last().unwrap() == name));
            IN_PRINTING.with(|f| f.borrow_mut().pop());
        }
        write!(f, "{s}>")
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

impl PartialEq for StructType {
    fn eq(&self, other: &Self) -> bool {
        match (&self.name, &other.name) {
            (Some(name), Some(other_name)) => name == other_name,
            (None, None) => {
                self.fields.len() == other.fields.len()
                    && self
                        .fields
                        .iter()
                        .zip(other.fields.iter())
                        .all(|(f1, f2)| f1.0 == f2.0 && f1.1 == f2.1)
            }
            _ => false,
        }
    }
}

impl Parsable for StructType {
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        _state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>
    where
        Self: Sized,
    {
        todo!()
    }
}

impl Eq for StructType {}

#[derive(Hash, PartialEq, Eq)]
pub struct PointerType {
    to: Ptr<TypeObj>,
}
impl_type!(PointerType, "ptr", "llvm");

impl PointerType {
    /// Get or create a new pointer type.
    pub fn get(ctx: &mut Context, to: Ptr<TypeObj>) -> Ptr<TypeObj> {
        Type::register_instance(PointerType { to }, ctx)
    }
    /// Get, if it already exists, a pointer type.
    pub fn get_existing(ctx: &Context, to: Ptr<TypeObj>) -> Option<Ptr<TypeObj>> {
        Type::get_instance(PointerType { to }, ctx)
    }

    /// Get the pointee type.
    pub fn get_pointee_type(&self) -> Ptr<TypeObj> {
        self.to
    }
}

impl Printable for PointerType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} <{}>",
            Self::get_type_id_static().disp(ctx),
            self.to.disp(ctx)
        )
    }
}

impl Parsable for PointerType {
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>
    where
        Self: Sized,
    {
        spaced(combine::between(token('<'), token('>'), type_parser())).parse_stream(state_stream)
    }
}

impl Verify for PointerType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

pub fn register(dialect: &mut Dialect) {
    StructType::register_type_in_dialect(dialect, StructType::parser_fn);
    PointerType::register_type_in_dialect(dialect, PointerType::parser_fn);
}

#[cfg(test)]
mod tests {

    use crate::{
        context::Context,
        dialects::{
            self,
            builtin::types::{IntegerType, Signedness},
            llvm::types::{PointerType, StructType},
        },
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
        r#type::{type_parser, Type},
    };

    #[test]
    fn test_struct() {
        let mut ctx = Context::new();
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signless);

        // Create an opaque struct since we want a recursive type.
        let list_struct = StructType::create_named(&mut ctx, "LinkedList", None);
        let list_struct_ptr = PointerType::get(&mut ctx, list_struct);
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

        let list_struct_2 = StructType::get_existing_named(&ctx, "LinkedList").unwrap();
        assert!(list_struct == list_struct_2);
        assert!(StructType::get_existing_named(&ctx, "LinkedList2").is_none());

        assert_eq!(
            list_struct
                .deref(&ctx)
                .downcast_ref::<StructType>()
                .unwrap()
                .disp(&ctx)
                .to_string(),
            "llvm.struct <LinkedList { data: builtin.integer <i64>, next: llvm.ptr <llvm.struct <LinkedList>>, }>"
        );

        let head_fields = vec![
            ("len".to_string(), int64_ptr),
            ("first".to_string(), list_struct_ptr),
        ];
        let head_struct = StructType::get_unnamed(&mut ctx, head_fields.clone());
        let head_struct2 = StructType::get_existing_unnamed(&ctx, head_fields).unwrap();
        assert!(head_struct == head_struct2);
        assert!(StructType::get_existing_unnamed(
            &ctx,
            vec![
                ("len".to_string(), int64_ptr),
                // The actual field is a LinkedList here, rather than a pointer type to it.
                ("first".to_string(), list_struct),
            ]
        )
        .is_none());
    }

    #[test]
    fn test_pointer_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register_instance(int64pointer_ptr, &mut ctx);
        assert_eq!(
            int64pointer_ptr.disp(&ctx).to_string(),
            "llvm.ptr <builtin.integer <si64>>"
        );
        assert!(int64pointer_ptr == PointerType::get(&mut ctx, int64_ptr));

        assert!(
            int64_ptr
                .deref(&ctx)
                .downcast_ref::<IntegerType>()
                .unwrap()
                .get_width()
                == 64
        );

        assert!(IntegerType::get_existing(&ctx, 32, Signedness::Signed).unwrap() == int32_1_ptr);
        assert!(PointerType::get_existing(&ctx, int64_ptr).unwrap() == int64pointer_ptr);
        assert!(
            int64pointer_ptr
                .deref(&ctx)
                .downcast_ref::<PointerType>()
                .unwrap()
                .get_pointee_type()
                == int64_ptr
        );
    }

    #[test]
    fn test_pointer_type_parsing() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);
        dialects::llvm::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "llvm.ptr <builtin.integer <si64>>".chars(),
            parsable::State { ctx: &mut ctx },
        );

        let res = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(&res.disp(&ctx).to_string(), "builtin.integer <si64>");
    }
}
