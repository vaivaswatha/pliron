use crate::{
    asmfmt::printers::{concat, enclosed, list_with_sep, type_header},
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::Dialect,
    error::Result,
    identifier::Identifier,
    impl_type, input_err_noloc,
    location::{Located, Location},
    parsable::{spaced, IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{self, ListSeparator, Printable},
    r#type::{type_parser, Type, TypeObj},
    verify_err_noloc,
};
use combine::{between, optional, parser::char::spaces, sep_by, token, Parser};
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
        concat((&self.field_name, ": ", self.field_type)).fmt(ctx, state, f)
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
#[derive(Debug)]
pub struct StructType {
    name: Option<String>,
    fields: Vec<StructField>,
    finalized: bool,
}
impl_type!(StructType, "struct", "llvm");

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
    ) -> Result<Ptr<TypeObj>> {
        let self_ptr = Type::register_instance(
            StructType {
                name: Some(name.to_string()),
                fields: fields.clone().unwrap_or_default(),
                finalized: fields.is_some(),
            },
            ctx,
        );
        // Verify that we created a new or equivalent existing type.
        let mut self_ref = self_ptr.deref_mut(ctx);
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
    pub fn get_unnamed(ctx: &mut Context, fields: Vec<StructField>) -> Ptr<TypeObj> {
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
    pub fn get_existing_named(ctx: &Context, name: &str) -> Option<Ptr<TypeObj>> {
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
    pub fn get_existing_unnamed(ctx: &Context, fields: Vec<StructField>) -> Option<Ptr<TypeObj>> {
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
        write!(f, "{} <", Self::get_type_id_static().disp(ctx))?;
        use std::cell::RefCell;
        // Ugly, but also the simplest way to avoid infinite recursion.
        // MLIR does the same: see LLVMTypeSyntax::printStructType.
        thread_local! {
            // We use a vec instead of a HashMap hoping that this isn't
            // going to be large, in which case vec would be faster.
            static IN_PRINTING: RefCell<Vec<String>>  = RefCell::new(vec![]);
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
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let body_parser = || {
            // Parse multiple type annotated fields separated by ','.
            let fields_parser = spaces().with(sep_by::<Vec<_>, _, _, _>(
                StructField::parser(()).skip(spaces()),
                token(',').skip(spaces()),
            ));
            // The body is multiple type annotated fields surrounded by '{' and '}'.
            between(token('{'), token('}'), fields_parser)
        };

        let named = spaced((combine::position(), Identifier::parser(())))
            .and(optional(spaced(body_parser())))
            .map(|((position, name), body_opt)| (position, Some(name), body_opt));
        let anonymous = spaced((combine::position(), body_parser()))
            .map(|(position, body)| (position, None::<Identifier>, Some(body)));

        // A struct type is named or anonymous.
        let mut struct_parser = between(token('<'), token('>'), named.or(anonymous));

        let src = state_stream
            .loc()
            .source()
            .expect("Expect Location::SrcPos for parser locations");
        let (pos, name_opt, body_opt) = struct_parser.parse_stream(state_stream).into_result()?.0;
        let ctx = &mut state_stream.state.ctx;
        if let Some(name) = name_opt {
            let loc = Location::SrcPos { src, pos };
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

#[derive(Hash, PartialEq, Eq, Debug)]
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
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        concat((type_header(self), " <", self.to, ">")).fmt(ctx, state, f)
    }
}

impl Parsable for PointerType {
    type Arg = ();
    type Parsed = Ptr<TypeObj>;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        combine::between(token('<'), token('>'), spaced(type_parser()))
            .parse_stream(state_stream)
            .map(|pointee_ty| PointerType::get(state_stream.state.ctx, pointee_ty))
            .into()
    }
}

impl Verify for PointerType {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}

pub fn register(dialect: &mut Dialect) {
    StructType::register_type_in_dialect(dialect, StructType::parser_fn);
    PointerType::register_type_in_dialect(dialect, PointerType::parser_fn);
}

#[cfg(test)]
mod tests {

    use expect_test::expect;

    use crate::{
        common_traits::Verify,
        context::Context,
        dialects::{
            self,
            builtin::types::{IntegerType, Signedness},
            llvm::types::{PointerType, StructErr, StructField, StructType},
        },
        error::{Error, ErrorKind, Result},
        location,
        parsable::{self, state_stream_from_iterator},
        printable::Printable,
        r#type::{type_parser, Type},
    };

    #[test]
    fn test_struct() -> Result<()> {
        let mut ctx = Context::new();
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signless);

        // Create an opaque struct since we want a recursive type.
        let list_struct = StructType::get_named(&mut ctx, "LinkedList", None)?;
        assert!(!StructType::is_finalized(&ctx, list_struct));
        let list_struct_ptr = PointerType::get(&mut ctx, list_struct);
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
            "llvm.struct <LinkedList { data: builtin.int <i64>, next: llvm.ptr <llvm.struct <LinkedList>> }>"
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

    #[test]
    fn test_pointer_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let int64pointer_ptr = PointerType { to: int64_ptr };
        let int64pointer_ptr = Type::register_instance(int64pointer_ptr, &mut ctx);
        assert_eq!(
            int64pointer_ptr.disp(&ctx).to_string(),
            "llvm.ptr <builtin.int <si64>>"
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
            "llvm.ptr <builtin.int <si64>>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(&res.disp(&ctx).to_string(), "llvm.ptr <builtin.int <si64>>");
    }

    #[test]
    fn test_struct_type_parsing() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);
        dialects::llvm::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "llvm.struct <LinkedList { data: builtin.int <i64>, next: llvm.ptr <llvm.struct <LinkedList>> }>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(&res.disp(&ctx).to_string(), "llvm.struct <LinkedList { data: builtin.int <i64>, next: llvm.ptr <llvm.struct <LinkedList>> }>");
    }

    #[test]
    fn test_struct_type_errs() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);
        dialects::llvm::register(&mut ctx);

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
}
