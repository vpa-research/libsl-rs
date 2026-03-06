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

    /// A type parameter.
    Param(usize),

    /// An inference variable.
    Var(usize),

    /// The null type.
    Null,
    // TODO: literal types.
}

impl Ty {
    pub fn as_constructed(&self) -> Option<&ConstructedTy> {
        match self {
            Self::Ctor(t) => Some(t),
            _ => None,
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    pub fn as_param(&self) -> Option<usize> {
        match *self {
            Self::Param(n) => Some(n),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct IntCtor {
    /// The number of bits comprising an integer.
    pub width: IntWidth,

    /// Whether the integer is signed.
    pub signed: bool,
}

impl IntCtor {
    pub const I8: Self = Self {
        width: IntWidth::I8,
        signed: true,
    };

    pub const I16: Self = Self {
        width: IntWidth::I16,
        signed: true,
    };

    pub const I32: Self = Self {
        width: IntWidth::I32,
        signed: true,
    };

    pub const I64: Self = Self {
        width: IntWidth::I64,
        signed: true,
    };

    pub const U8: Self = Self {
        width: IntWidth::I8,
        signed: false,
    };

    pub const U16: Self = Self {
        width: IntWidth::I16,
        signed: false,
    };

    pub const U32: Self = Self {
        width: IntWidth::I32,
        signed: false,
    };

    pub const U64: Self = Self {
        width: IntWidth::I64,
        signed: false,
    };
}

/// The width of an integer, determining its range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Clone, Copy)]
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
    Set,
    Pointer,
    Void,
}

impl BuiltinTyCtor {
    pub fn variance(&self) -> &'static [Variance] {
        match self {
            Self::Any => &[],
            Self::Nothing => &[],
            Self::Bool => &[],
            Self::Char => &[],
            Self::String => &[],
            Self::Int(_) => &[],
            Self::Float(_) => &[],
            Self::Array => &[Variance::Invariant],
            Self::Set => &[Variance::Covariant],
            Self::Pointer => &[Variance::Invariant],
            Self::Void => &[],
        }
    }

    pub fn as_int(&self) -> Option<&IntCtor> {
        match self {
            Self::Int(c) => Some(c),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<&FloatCtor> {
        match self {
            Self::Float(c) => Some(c),
            _ => None,
        }
    }
}

/// The type obtained by applying type arguments to a type constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructedTy {
    /// The type constructor.
    pub ctor: DefId,

    /// The type arguments.
    pub args: Vec<TyId>,
}
