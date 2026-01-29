//! LibSL types.
//!
//! The same way that expressions evaluate to values, type expressions conceptually evaluate to
//! types. For instance, the type expression `int8` is not necessarily the same as the 8-bit signed
//! integer type, since the user may (however nonsensical this may be) define their own type named
//! `int8`, in which case the expression would refer to it. Therefore, types form a distinct
//! hierarchy.

use slotmap::new_key_type;

use crate::ast::Variance;
use crate::sema::def::DefId;

new_key_type! {
    pub struct TyId;
}

/// A LibSL type.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    #[default]
    Error,

    /// A type constructed by applying type parameters to a type constructor.
    Ctor(ConstructedTy),

    /// An inference variable.
    Var(usize),

    /// The null type.
    Null,

    // TODO: literal types.
}

#[derive(Debug, Clone)]
pub struct IntCtor {
    /// The number of bits comprising an integer.
    pub width: IntWidth,

    /// Whether the integer is signed.
    pub signed: bool,
}

/// The width of an integer, determining its range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntWidth {
    /// 8 bits.
    I8,

    /// 16 bits.
    I16,

    /// 32 bits.
    I32,

    /// 64 bits.
    I64,
}

impl IntWidth {
    pub fn to_usize(self) -> usize {
        match self {
            IntWidth::I8 => 8,
            IntWidth::I16 => 16,
            IntWidth::I32 => 32,
            IntWidth::I64 => 64,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FloatCtor {
    F32,
    F64,
}

impl FloatCtor {
    pub fn width(self) -> usize {
        match self {
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }
}

#[derive(Debug, Clone)]
pub enum BuiltinTyCtor {
    Any,
    Nothing,
    Bool,
    Char,
    String,
    Int(IntCtor),
    Float(FloatCtor),
    Array,
    Void,
}

/// The type obtained by applying type arguments to a type constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructedTy {
    /// The type constructor.
    pub ctor: DefId,

    /// The type arguments.
    pub args: Vec<ConstructedTyArg>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstructedTyArg {
    Ty(Option<Variance>, TyId),
    Wildcard,
}
