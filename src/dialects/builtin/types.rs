use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    dialect::Dialect,
    error::CompilerError,
    impl_type,
    r#type::{Type, TypeObj},
    storage_uniquer::TypeValueHash,
    with_context::AttachContext,
};

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub enum Signedness {
    Signed,
    Unsigned,
    Signless,
}

#[derive(Hash, PartialEq, Eq)]
pub struct IntegerType {
    width: u64,
    signedness: Signedness,
}
impl_type!(IntegerType, "integer", "builtin");

impl IntegerType {
    /// Get or create a new integer type.
    pub fn get(ctx: &mut Context, width: u64, signedness: Signedness) -> Ptr<TypeObj> {
        Type::register_instance(IntegerType { width, signedness }, ctx)
    }
    /// Get, if it already exists, an integer type.
    pub fn get_existing(ctx: &Context, width: u64, signedness: Signedness) -> Option<Ptr<TypeObj>> {
        Type::get_instance(IntegerType { width, signedness }, ctx)
    }

    /// Get width.
    pub fn get_width(&self) -> u64 {
        self.width
    }

    /// Get signedness.
    pub fn get_signedness(&self) -> Signedness {
        self.signedness
    }
}

impl DisplayWithContext for IntegerType {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.signedness {
            Signedness::Signed => write!(f, "si{}", self.width),
            Signedness::Unsigned => write!(f, "ui{}", self.width),
            Signedness::Signless => write!(f, "i{}", self.width),
        }
    }
}

impl Verify for IntegerType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

/// Map from a list of inputs to a list of results
///
/// See MLIR's [FunctionType](https://mlir.llvm.org/docs/Dialects/Builtin/#functiontype).
///
#[derive(Hash, PartialEq, Eq)]
pub struct FunctionType {
    /// Function arguments / inputs.
    inputs: Vec<Ptr<TypeObj>>,
    /// Function results / outputs.
    results: Vec<Ptr<TypeObj>>,
}
impl_type!(FunctionType, "Function", "builtin");

impl FunctionType {
    /// Get or create a new Function type.
    pub fn get(
        ctx: &mut Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> Ptr<TypeObj> {
        Type::register_instance(FunctionType { inputs, results }, ctx)
    }
    /// Get, if it already exists, a Function type.
    pub fn get_existing(
        ctx: &Context,
        inputs: Vec<Ptr<TypeObj>>,
        results: Vec<Ptr<TypeObj>>,
    ) -> Option<Ptr<TypeObj>> {
        Type::get_instance(FunctionType { inputs, results }, ctx)
    }

    /// Get a reference to the function input / argument types.
    pub fn get_inputs(&self) -> &Vec<Ptr<TypeObj>> {
        &self.inputs
    }

    /// Get a reference to the function result / output types.
    pub fn get_results(&self) -> &Vec<Ptr<TypeObj>> {
        &self.results
    }
}

impl DisplayWithContext for FunctionType {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(")?;
        for arg in &self.inputs {
            write!(f, "{}", arg.with_ctx(ctx))?;
        }
        write!(f, ") -> (")?;
        for res in &self.results {
            write!(f, "{},", res.with_ctx(ctx))?;
        }
        write!(f, ")")
    }
}

impl Verify for FunctionType {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

pub fn register(dialect: &mut Dialect) {
    IntegerType::register_type_in_dialect(dialect);
    FunctionType::register_type_in_dialect(dialect);
}

#[cfg(test)]
mod tests {
    use super::FunctionType;
    use crate::{
        context::Context,
        dialects::builtin::types::{IntegerType, Signedness},
    };
    #[test]
    fn test_integer_types() {
        let mut ctx = Context::new();

        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int32_2_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let uint32_ptr = IntegerType::get(&mut ctx, 32, Signedness::Unsigned);

        assert!(int32_1_ptr.deref(&ctx).hash_type() == int32_2_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != int64_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr.deref(&ctx).hash_type() != uint32_ptr.deref(&ctx).hash_type());
        assert!(int32_1_ptr == int32_2_ptr);
        assert!(int32_1_ptr != int64_ptr);
        assert!(int32_1_ptr != uint32_ptr);

        assert!(int32_1_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_1_ptr);
        assert!(int32_2_ptr.deref(&ctx).get_self_ptr(&ctx) == int32_2_ptr);
        assert!(int64_ptr.deref(&ctx).get_self_ptr(&ctx) == int64_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) == uint32_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int32_1_ptr);
        assert!(uint32_ptr.deref(&ctx).get_self_ptr(&ctx) != int64_ptr);
    }

    #[test]
    fn test_function_types() {
        let mut ctx = Context::new();
        let int32_1_ptr = IntegerType::get(&mut ctx, 32, Signedness::Signed);
        let int64_ptr = IntegerType::get(&mut ctx, 64, Signedness::Signed);

        let ft = FunctionType::get(&mut ctx, vec![int32_1_ptr], vec![int64_ptr]).deref(&ctx);
        let ft_ref = ft.downcast_ref::<FunctionType>().unwrap();
        assert!(ft_ref.get_inputs()[0] == int32_1_ptr && ft_ref.get_results()[0] == int64_ptr);
    }
}
