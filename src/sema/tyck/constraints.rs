//! Type constraint solving.

use std::collections::HashSet;

use slotmap::{SlotMap, new_key_type};

use crate::{AccessId, ExprId};
use crate::diag::DiagCtx;
use crate::sema::def::DefId;
use crate::sema::ty::TyId;
use crate::sema::tyck::Pass;

new_key_type! {
    pub struct ConstrId;
}

#[derive(Debug, Default)]
pub struct ConstrSet {
    constrs: SlotMap<ConstrId, Constr>,
    unprocessed: Vec<ConstrId>,
}

#[derive(Debug, Clone)]
pub enum ConstrProvenance {
    /// Derived from another constraint.
    Constr(ConstrId),

    /// Comes from an expression's typing requirements.
    Expr(ExprId),

    /// Comes from an access's typing requirements.
    Access(AccessId),
}

#[derive(Debug, Clone)]
pub struct Constr {
    pub provenance: ConstrProvenance,
    pub kind: ConstrKind,
}

#[derive(Debug, Clone)]
pub enum ConstrKind {
    /// The left type is a subtype of the right type.
    Sub(TyId, TyId),

    /// The left type equals the right type.
    ///
    /// Note that this requires the two types to be fully identical, and is a stronger requirement
    /// than type equivalence (wherein lhs <: rhs and rhs <: lhs).
    Eq(TyId, TyId),
}

#[derive(Debug, Default)]
pub struct BoundSet {
    vars: Vec<VarConstr>,
}

#[derive(Debug, Clone)]
pub enum VarProvenance {
    /// The type of a variable.
    Var(DefId),
}

#[derive(Debug)]
pub struct VarConstr {
    /// Where the inference variable came from.
    pub provenance: VarProvenance,

    /// Lower bounds.
    ///
    /// Constrain the variable to be a supertype of the union of these types.
    pub lower: HashSet<TyId>,

    /// Upper bounds.
    ///
    /// Constrain the variable to be a subtype of the intersection of these types.
    pub upper: HashSet<TyId>,

    /// The equality bound.
    pub eq: Option<TyId>,
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {}
