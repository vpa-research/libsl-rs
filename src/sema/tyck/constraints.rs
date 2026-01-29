//! Type constraint solving.

use std::collections::HashSet;

use slotmap::{SlotMap, new_key_type};

use crate::diag::DiagCtx;
use crate::sema::def::DefId;
use crate::sema::ty::TyId;
use crate::sema::tyck::Pass;
use crate::{AccessId, ExprId, ast};

new_key_type! {
    pub struct ConstrId;
}

#[derive(Debug, Default)]
pub struct ConstrSet {
    constrs: SlotMap<ConstrId, Constr>,
    unprocessed: Vec<ConstrId>,
}

impl ConstrSet {
    pub fn add(&mut self, constr: Constr) -> ConstrId {
        let id = self.constrs.insert(constr);
        self.unprocessed.push(id);

        id
    }
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

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    pub fn constr_sub(&mut self, lhs: TyId, rhs: TyId, provenance: ConstrProvenance) {
        self.sema.tyck.constrs.add(Constr {
            provenance,
            kind: ConstrKind::Sub(lhs, rhs),
        });
    }

    pub fn constr_eq(&mut self, lhs: TyId, rhs: TyId, provenance: ConstrProvenance) {
        self.sema.tyck.constrs.add(Constr {
            provenance,
            kind: ConstrKind::Eq(lhs, rhs),
        });
    }

    pub fn constr_expr(&mut self, expr_id: ExprId, ty_id: TyId) {
        let expr = &self.sema.libsl.exprs[expr_id];

        match &expr.kind {
            ast::ExprKind::Dummy => unreachable!(),
            ast::ExprKind::PrimitiveLit(e) => todo!(),
            ast::ExprKind::ArrayLit(e) => todo!(),
            ast::ExprKind::SetLit(e) => todo!(),
            ast::ExprKind::Access(e) => todo!(),
            ast::ExprKind::Prev(e) => todo!(),
            ast::ExprKind::ProcCall(e) => todo!(),
            ast::ExprKind::ActionCall(e) => todo!(),
            ast::ExprKind::Instantiate(e) => todo!(),
            ast::ExprKind::HasConcept(e) => todo!(),
            ast::ExprKind::Cast(e) => todo!(),
            ast::ExprKind::TyCompare(e) => todo!(),
            ast::ExprKind::Unary(e) => todo!(),
            ast::ExprKind::Binary(e) => todo!(),
        }
    }
}
