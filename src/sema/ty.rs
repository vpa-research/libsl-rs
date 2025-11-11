//! LibSL types.
//!
//! The same way that expressions evaluate to values, type expressions conceptually evaluate to
//! types. For instance, the type expression `int8` is not necessarily the same as the 8-bit signed
//! integer type, since the user may (however nonsensical this may be) define their own type named
//! `int8`, in which case the expression would refer to it. Therefore, types form a distinct
//! hierarchy.

use slotmap::new_key_type;

new_key_type! {
    pub struct TyId;
}

/// A LibSL type.
#[derive(Debug, Default, Clone)]
pub enum Ty {
    /// A dummy type erroneous expressions are typed as.
    #[default]
    Error,

    /// A type constructed by applying type parameters to a type constructor.
    Ctor(ConstructedTy),

    /// The `Any` type, the supertype of all other types.
    Any,

    /// The `Nothing` type, the subtype of all other types.
    Nothing,

    /// The boolean type.
    Bool,

    /// The character type.
    Char,

    /// A floating-point number type.
    Float(TyFloat),

    /// An integer type
    Int(TyInt),
}

/// A type constructor.
///
/// When applied to type parameters, produces a [constructed type][Ty::Ctor].
#[derive(Debug, Clone)]
pub enum TyCtor {}

impl TyCtor {
    pub fn param_count(&self) -> usize {
        match *self {}
    }

    pub fn apply(&self, params: Vec<TyId>) -> ConstructedTy {
        todo!()
    }
}

/// The type obtained by applying type parameters to a type constructor.
#[derive(Debug, Clone)]
pub struct ConstructedTy {
    /// The type constructor.
    pub ctor: TyCtor,

    /// The type parameters.
    pub params: Vec<TyId>,
}

/// A floating-point number type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyFloat {
    F32,
    F64,
}

impl TyFloat {
    pub fn width(self) -> usize {
        match self {
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }
}

/// An integer type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyInt {
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
