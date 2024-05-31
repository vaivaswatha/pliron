//! [Type]s defined in the LLVM dialect.

use combine::{between, optional, parser::char::spaces, token, Parser};
use pliron::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    identifier::Identifier,
    impl_verify_succ, input_err_noloc,
    irfmt::{
        parsers::{delimited_list_parser, location, spaced, type_parser, u64_parser},
        printers::{enclosed, list_with_sep},
    },
    location::Located,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, ListSeparator, Printable},
    r#type::{Type, TypeObj, TypePtr},
    verify_err_noloc,
};
use pliron_derive::def_type;
use thiserror::Error;

use std::hash::Hash;

/// A field in a [StructType].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StructField {
    pub field_name: Identifier,
    pub field_type: Ptr<TypeObj>,
}

impl Printable for StructField {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{}: {}",
            self.field_name,
            self.field_type.print(ctx, state)
        )
    }
}

impl Parsable for StructField {
    type Arg = ();
    type Parsed = StructField;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        // Parse a single type annotated field.
        (
            spaced(Identifier::parser(())),
            token(':'),
            spaced(type_parser()),
        )
            .parse_stream(state_stream)
            .map(|(field_name, _, field_type)| StructField {
                field_name,
                field_type,
            })
            .into()
    }
}

/// Represents a c-like struct type.
/// Limitations and warnings on its usage are similar to that in MLIR.
/// `<https://mlir.llvm.org/docs/Dialects/LLVM/#structure-types>`
///   1. Anonymous (aka unnamed) structs cannot be recursive.
///   2. Named structs are uniqued *only* by name, and may be recursive.
///      Call "set_fields" after creation to set recursive types.
///   3. LLVM calls anonymous structs as literal structs and
///      named structs as identified structs.
#[def_type("llvm.struct")]
#[derive(Debug)]
pub struct StructType {
    name: Option<String>,
    fields: Vec<StructField>,
    finalized: bool,
}

impl StructType {
    /// Get or create a new named StructType.
    /// If fields is None, it indicates an opaque (i.e., not finalized) struct.
    /// Opaque structs must be finalized (by passing non-none `fields`) for verify() to succeed.
    /// Opaque structs are an intermediary in creating recursive types.
    /// Returns an error when the name is already registered but the fields don't match.
    pub fn get_named(
        ctx: &mut Context,
        name: &str,
        fields: Option<Vec<StructField>>,
    ) -> Result<TypePtr<Self>> {
        let self_ptr = Type::register_instance(
            StructType {
                name: Some(name.to_string()),
                fields: fields.clone().unwrap_or_default(),
                finalized: fields.is_some(),
            },
            ctx,
        );
        // Verify that we created a new or equivalent existing type.
        let mut self_ref = self_ptr.to_ptr().deref_mut(ctx);
        let self_ref = self_ref.downcast_mut::<StructType>().unwrap();
        assert!(self_ref.name.as_ref().unwrap() == name);
        if let Some(fields) = fields {
            if !self_ref.finalized {
                self_ref.fields = fields;
                self_ref.finalized = true;
            } else if self_ref.fields != fields {
                input_err_noloc!(StructErr::ExistingMismatch(name.into()))?
            }
        }
        Ok(self_ptr)
    }

    /// Get or create a new unnamed (anonymous) struct.
    /// These are finalized upon creation, and uniqued based on the fields.
    pub fn get_unnamed(ctx: &mut Context, fields: Vec<StructField>) -> TypePtr<Self> {
        Type::register_instance(
            StructType {
                name: None,
                fields,
                finalized: true,
            },
            ctx,
        )
    }

    /// Is this struct finalized? Returns false for non [StructType]s.
    pub fn is_finalized(ctx: &Context, ty: Ptr<TypeObj>) -> bool {
        ty.deref(ctx)
            .downcast_ref::<StructType>()
            .filter(|s| s.finalized)
            .is_some()
    }

    /// If a named struct already exists, get a pointer to it.
    pub fn get_existing_named(ctx: &Context, name: &str) -> Option<TypePtr<Self>> {
        Type::get_instance(
            StructType {
                name: Some(name.to_string()),
                // Named structs are uniqued only on the name.
                fields: vec![],
                finalized: false,
            },
            ctx,
        )
    }

    /// If an unnamed struct already exists, get a pointer to it.
    pub fn get_existing_unnamed(ctx: &Context, fields: Vec<StructField>) -> Option<TypePtr<Self>> {
        Type::get_instance(
            StructType {
                name: None,
                fields,
                finalized: true,
            },
            ctx,
        )
    }

    /// Get type of the idx'th field.
    pub fn field_type(&self, field_idx: usize) -> Ptr<TypeObj> {
        self.fields[field_idx].field_type
    }

    /// Get name of the idx'th field.
    pub fn field_name(&self, field_idx: usize) -> Identifier {
        self.fields[field_idx].field_name.clone()
    }

    /// Get the number of fields this struct has
    pub fn num_fields(&self) -> usize {
        self.fields.len()
    }
}

#[derive(Debug, Error)]
pub enum StructErr {
    #[error("struct {0} is not finalized")]
    NotFinalized(String),
    #[error("struct {0} already exists and is different")]
    ExistingMismatch(String),
}

impl Verify for StructType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        if !self.finalized {
            return verify_err_noloc!(StructErr::NotFinalized(
                self.name.clone().unwrap_or("<anonymous>".into())
            ));
        }
        Ok(())
    }
}

impl Printable for StructType {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "<")?;

        use std::cell::RefCell;
        // Ugly, but also the simplest way to avoid infinite recursion.
        // MLIR does the same: see LLVMTypeSyntax::printStructType.
        thread_local! {
            // We use a vec instead of a HashMap hoping that this isn't
            // going to be large, in which case vec would be faster.
            static IN_PRINTING: RefCell<Vec<String>>  = const { RefCell::new(vec![]) };
        }
        if let Some(name) = &self.name {
            let in_printing = IN_PRINTING.with(|f| f.borrow().contains(name));
            if in_printing {
                return write!(f, "{}>", name.clone());
            }
            IN_PRINTING.with(|f| f.borrow_mut().push(name.clone()));
            write!(f, "{name} ")?;
        }

        enclosed(
            "{ ",
            " }",
            list_with_sep(&self.fields, ListSeparator::CharSpace(',')),
        )
        .fmt(ctx, state, f)?;

        // Done processing this struct. Remove it from the stack.
        if let Some(name) = &self.name {
            debug_assert!(IN_PRINTING.with(|f| f.borrow().last().unwrap() == name));
            IN_PRINTING.with(|f| f.borrow_mut().pop());
        }
        write!(f, ">")
    }
}

impl Hash for StructType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.name {
            Some(name) => name.hash(state),
            None => self.fields.iter().for_each(
                |StructField {
                     field_name,
                     field_type,
                 }| {
                    field_name.hash(state);
                    field_type.hash(state);
                },
            ),
        }
    }
}

impl PartialEq for StructType {
    fn eq(&self, other: &Self) -> bool {
        match (&self.name, &other.name) {
            (Some(name), Some(other_name)) => name == other_name,
            (None, None) => {
                self.fields.len() == other.fields.len()
                    && self.fields.iter().zip(other.fields.iter()).all(|(f1, f2)| {
                        f1.field_name == f2.field_name && f1.field_type == f2.field_type
                    })
            }
            _ => false,
        }
    }
}

impl Parsable for StructType {
    type Arg = ();
    type Parsed = TypePtr<Self>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let body_parser = || {
            // Parse multiple type annotated fields separated by ',', all of it delimited by braces.
            delimited_list_parser('{', '}', ',', StructField::parser(()))
        };

        let named = spaced((location(), Identifier::parser(())))
            .and(optional(spaced(body_parser())))
            .map(|((loc, name), body_opt)| (loc, Some(name), body_opt));
        let anonymous = spaced((location(), body_parser()))
            .map(|(loc, body)| (loc, None::<Identifier>, Some(body)));

        // A struct type is named or anonymous.
        let mut struct_parser = between(token('<'), token('>'), named.or(anonymous));

        let (loc, name_opt, body_opt) = struct_parser.parse_stream(state_stream).into_result()?.0;
        let ctx = &mut state_stream.state.ctx;
        if let Some(name) = name_opt {
            StructType::get_named(ctx, &name, body_opt)
                .map_err(|mut err| {
                    err.set_loc(loc);
                    err
                })
                .into_parse_result()
        } else {
            Ok(StructType::get_unnamed(
                ctx,
                body_opt.expect("Without a name, a struct type must have a body."),
            ))
            .into_parse_result()
        }
    }
}

impl Eq for StructType {}

/// An opaque pointer, corresponding to LLVM's pointer type.
#[def_type("llvm.ptr")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct PointerType;

impl PointerType {
    /// Get or create a new pointer type.
    pub fn get(ctx: &mut Context) -> TypePtr<Self> {
        Type::register_instance(PointerType, ctx)
    }
    /// Get, if it already exists, a pointer type.
    pub fn get_existing(ctx: &Context) -> Option<TypePtr<Self>> {
        Type::get_instance(PointerType, ctx)
    }
}

impl Printable for PointerType {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        _f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        Ok(())
    }
}

impl Parsable for PointerType {
    type Arg = ();
    type Parsed = TypePtr<Self>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        Ok(PointerType::get(state_stream.state.ctx)).into_parse_result()
    }
}

impl_verify_succ!(PointerType);

/// Array type, corresponding to LLVM's array type.
#[def_type("llvm.array")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct ArrayType {
    elem: Ptr<TypeObj>,
    size: usize,
}

impl ArrayType {
    /// Get or create a new array type.
    pub fn get(ctx: &mut Context, elem: Ptr<TypeObj>, size: usize) -> TypePtr<Self> {
        Type::register_instance(ArrayType { elem, size }, ctx)
    }
    /// Get, if it already exists, an array type.
    pub fn get_existing(ctx: &Context, elem: Ptr<TypeObj>, size: usize) -> Option<TypePtr<Self>> {
        Type::get_instance(ArrayType { elem, size }, ctx)
    }

    /// Get array element type.
    pub fn elem_type(&self) -> Ptr<TypeObj> {
        self.elem
    }

    /// Get array size.
    pub fn size(&self) -> usize {
        self.size
    }
}

impl Printable for ArrayType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "[{} x {}]", self.size, self.elem.disp(ctx))
    }
}

impl Parsable for ArrayType {
    type Arg = ();
    type Parsed = TypePtr<Self>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        combine::between(
            token('['),
            token(']'),
            spaced((u64_parser(), spaced(token('x')), type_parser())),
        )
        .parse_stream(state_stream)
        .map(|(size, _, elem)| ArrayType::get(state_stream.state.ctx, elem, size as usize))
        .into()
    }
}
impl_verify_succ!(ArrayType);

#[def_type("llvm.void")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct VoidType;

impl VoidType {
    /// Get or create a new void type.
    pub fn get(ctx: &mut Context) -> TypePtr<Self> {
        Type::register_instance(Self {}, ctx)
    }
}

impl Printable for VoidType {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        _f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        Ok(())
    }
}

impl Parsable for VoidType {
    type Arg = ();

    type Parsed = TypePtr<VoidType>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        Ok(VoidType::get(state_stream.state.ctx)).into_parse_result()
    }
}

impl_verify_succ!(VoidType);

#[def_type("llvm.func")]
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct FuncType {
    res: Ptr<TypeObj>,
    args: Vec<Ptr<TypeObj>>,
}

impl FuncType {
    /// Get or create a new Func type.
    pub fn get(ctx: &mut Context, res: Ptr<TypeObj>, args: Vec<Ptr<TypeObj>>) -> TypePtr<Self> {
        Type::register_instance(FuncType { res, args }, ctx)
    }
}

impl_verify_succ!(FuncType);

impl Printable for FuncType {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "<{} ({})>",
            self.res.disp(ctx),
            list_with_sep(&self.args, ListSeparator::CharSpace(',')).disp(ctx)
        )
    }
}

impl Parsable for FuncType {
    type Arg = ();

    type Parsed = TypePtr<FuncType>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let type_list_parser = spaced(delimited_list_parser('(', ')', ',', type_parser()));
        spaced(between(
            token('<'),
            token('>'),
            spaces().with(type_parser()).and(type_list_parser),
        ))
        .parse_stream(state_stream)
        .map(|(res, args)| FuncType::get(state_stream.state.ctx, res, args))
        .into_result()
    }
}

pub fn register(dialect: &mut Dialect) {
    VoidType::register_type_in_dialect(dialect, VoidType::parser_fn);
    StructType::register_type_in_dialect(dialect, StructType::parser_fn);
    PointerType::register_type_in_dialect(dialect, PointerType::parser_fn);
    FuncType::register_type_in_dialect(dialect, FuncType::parser_fn);
}

#[cfg(test)]
mod tests {

    use crate as llvm;
    use combine::{eof, token, Parser};
    use expect_test::expect;
    use pliron_derive::def_type;

    use crate::types::{FuncType, StructErr, StructField, StructType, VoidType};
    use pliron::{
        builtin::{
            self,
            types::{IntegerType, Signedness},
        },
        common_traits::Verify,
        context::{Context, Ptr},
        dialect::DialectName,
        error::{Error, ErrorKind, Result},
        impl_verify_succ,
        irfmt::parsers::{spaced, type_parser},
        location,
        parsable::{self, state_stream_from_iterator, Parsable, ParseResult, StateStream},
        printable::{self, Printable},
        r#type::{Type, TypeObj, TypePtr},
    };

    #[test]
    fn test_struct() -> Result<()> {
        let mut ctx = Context::new();
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signless).into();

        // Create an opaque struct since we want a recursive type.
        let list_struct = StructType::get_named(&mut ctx, "LinkedList", None)?.into();
        assert!(!StructType::is_finalized(&ctx, list_struct));
        let list_struct_ptr = TypedPointerType::get(&mut ctx, list_struct).into();
        let fields = vec![
            StructField {
                field_name: "data".into(),
                field_type: int64_ptr,
            },
            StructField {
                field_name: "next".into(),
                field_type: list_struct_ptr,
            },
        ];
        // Finalize the type now.
        StructType::get_named(&mut ctx, "LinkedList", Some(fields))?;
        assert!(StructType::is_finalized(&ctx, list_struct));

        let list_struct_2 = StructType::get_existing_named(&ctx, "LinkedList")
            .unwrap()
            .into();
        assert!(list_struct == list_struct_2);
        assert!(StructType::get_existing_named(&ctx, "LinkedList2").is_none());

        assert_eq!(
            list_struct.disp(&ctx).to_string(),
            "llvm.struct<LinkedList { data: builtin.int<i64>, next: llvm.typed_ptr<llvm.struct<LinkedList>> }>"
        );

        let head_fields = vec![
            StructField {
                field_name: "len".into(),
                field_type: int64_ptr,
            },
            StructField {
                field_name: "first".into(),
                field_type: list_struct_ptr,
            },
        ];
        let head_struct = StructType::get_unnamed(&mut ctx, head_fields.clone());
        let head_struct2 = StructType::get_existing_unnamed(&ctx, head_fields).unwrap();
        assert!(head_struct == head_struct2);
        assert!(StructType::get_existing_unnamed(
            &ctx,
            vec![
                StructField {
                    field_name: "len".into(),
                    field_type: int64_ptr
                },
                // The actual field is a LinkedList here, rather than a pointer type to it.
                StructField {
                    field_name: "first".into(),
                    field_type: list_struct
                },
            ]
        )
        .is_none());

        Ok(())
    }

    /// A pointer type that knows the type it points to.
    /// This used to be in LLVM earlier, but the latest version
    /// is now type-erased (https://llvm.org/docs/OpaquePointers.html)
    #[def_type("llvm.typed_ptr")]
    #[derive(Hash, PartialEq, Eq, Debug)]
    pub struct TypedPointerType {
        to: Ptr<TypeObj>,
    }

    impl TypedPointerType {
        /// Get or create a new pointer type.
        pub fn get(ctx: &mut Context, to: Ptr<TypeObj>) -> TypePtr<Self> {
            Type::register_instance(TypedPointerType { to }, ctx)
        }
        /// Get, if it already exists, a pointer type.
        pub fn get_existing(ctx: &Context, to: Ptr<TypeObj>) -> Option<TypePtr<Self>> {
            Type::get_instance(TypedPointerType { to }, ctx)
        }

        /// Get the pointee type.
        pub fn get_pointee_type(&self) -> Ptr<TypeObj> {
            self.to
        }
    }

    impl Printable for TypedPointerType {
        fn fmt(
            &self,
            ctx: &Context,
            _state: &printable::State,
            f: &mut core::fmt::Formatter<'_>,
        ) -> core::fmt::Result {
            write!(f, "<{}>", self.to.disp(ctx))
        }
    }

    impl Parsable for TypedPointerType {
        type Arg = ();
        type Parsed = TypePtr<Self>;

        fn parse<'a>(
            state_stream: &mut StateStream<'a>,
            _arg: Self::Arg,
        ) -> ParseResult<'a, Self::Parsed>
        where
            Self: Sized,
        {
            combine::between(token('<'), token('>'), spaced(type_parser()))
                .parse_stream(state_stream)
                .map(|pointee_ty| TypedPointerType::get(state_stream.state.ctx, pointee_ty))
                .into()
        }
    }

    impl_verify_succ!(TypedPointerType);

    #[test]
    fn test_pointer_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed).into();

        let int64pointer_ptr = TypedPointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register_instance(int64pointer_ptr, &mut ctx);
        assert_eq!(
            int64pointer_ptr.disp(&ctx).to_string(),
            "llvm.typed_ptr<builtin.int<si64>>"
        );
        assert!(int64pointer_ptr == TypedPointerType::get(&mut ctx, int64_ptr));

        assert!(
            int64_ptr
                .deref(&ctx)
                .downcast_ref::<IntegerType>()
                .unwrap()
                .get_width()
                == 64
        );

        assert!(IntegerType::get_existing(&ctx, 32, Signedness::Signed).unwrap() == int32_1_ptr);
        assert!(TypedPointerType::get_existing(&ctx, int64_ptr).unwrap() == int64pointer_ptr);
        assert!(int64pointer_ptr.deref(&ctx).get_pointee_type() == int64_ptr);
    }

    #[test]
    fn test_pointer_type_parsing() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);
        llvm::register(&mut ctx);
        TypedPointerType::register_type_in_dialect(
            &mut ctx.dialects.get_mut(&DialectName::new("llvm")).unwrap(),
            TypedPointerType::parser_fn,
        );

        let state_stream = state_stream_from_iterator(
            "llvm.typed_ptr <builtin.int <si64>>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(
            &res.disp(&ctx).to_string(),
            "llvm.typed_ptr<builtin.int<si64>>"
        );
    }

    #[test]
    fn test_struct_type_parsing() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);
        llvm::register(&mut ctx);
        TypedPointerType::register_type_in_dialect(
            &mut ctx.dialects.get_mut(&DialectName::new("llvm")).unwrap(),
            TypedPointerType::parser_fn,
        );

        let state_stream = state_stream_from_iterator(
            "llvm.struct<LinkedList { data: builtin.int<i64>, next: llvm.typed_ptr<llvm.struct<LinkedList>> }>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(&res.disp(&ctx).to_string(),
            "llvm.struct<LinkedList { data: builtin.int<i64>, next: llvm.typed_ptr<llvm.struct<LinkedList>> }>");
    }

    #[test]
    fn test_struct_type_errs() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);
        llvm::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "llvm.struct < My1 { f1: builtin.int<i8> } >".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let _ = type_parser().parse(state_stream).unwrap().0;

        let state_stream = state_stream_from_iterator(
            "llvm.struct < My1 { f1: builtin.int<i16> } >".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 15
            struct My1 already exists and is different
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "llvm.struct < My2 >".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );
        let res = type_parser().parse(state_stream).unwrap().0;
        matches!(
            &res.verify(&ctx),
            Err (Error { kind: ErrorKind::VerificationFailed, err, loc: _ })
                if err.is::<StructErr>()
        );
    }

    #[test]
    fn test_functype_parsing() {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);
        llvm::register(&mut ctx);

        let si32 = IntegerType::get(&mut ctx, 32, Signedness::Signed);

        let input = "llvm.func<llvm.void (builtin.int<si32>)>";
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().and(eof()).parse(state_stream).unwrap().0 .0;

        let void_ty = VoidType::get(&mut ctx);
        assert!(res == FuncType::get(&mut ctx, void_ty.to_ptr(), vec![si32.into()]).into());
        assert_eq!(input, &res.disp(&ctx).to_string());
    }
}
