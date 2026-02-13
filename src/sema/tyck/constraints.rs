//! Type constraint solving.

use std::iter;
use std::sync::LazyLock;

use slotmap::{SlotMap, SparseSecondaryMap, new_key_type};

use crate::ast::Variance;
use crate::diag::DiagCtx;
use crate::sema::def::DefId;
use crate::sema::ty::{BuiltinTyCtor, ConstructedTy, Ty, TyId};
use crate::sema::tyck::Pass;
use crate::sema::{Result, Sema};
use crate::{AccessId, ExprId, ast};

new_key_type! {
    pub struct ConstrId;
}

#[derive(Debug, Clone, Default)]
enum ConstrStatus {
    #[default]
    Sat,

    Processing,

    Unsat,
}

impl ConstrStatus {
    fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    fn is_processing(&self) -> bool {
        matches!(self, Self::Processing)
    }
}

#[derive(Debug, Clone, Copy)]
enum VarBound {
    Lower(TyId),
    Upper(TyId),
    Eq(TyId),
}

#[derive(Debug, Clone, Default)]
pub struct ConstrSet {
    constrs: SlotMap<ConstrId, Constr>,
    unprocessed: Vec<ConstrId>,
    bounds: BoundSet,
    status: ConstrStatus,
}

impl ConstrSet {
    pub fn add(&mut self, sema: &mut Sema<'_>, diag: &mut impl DiagCtx, constr: Constr) -> Result {
        if self.status.is_unsat() {
            return Err(());
        }

        let id = self.constrs.insert(constr);
        self.unprocessed.push(id);

        if !self.status.is_processing() {
            return self.process(sema, diag);
        }

        Ok(())
    }

    fn process(&mut self, sema: &mut Sema<'_>, diag: &mut impl DiagCtx) -> Result {
        assert!(!self.status.is_processing());

        if self.status.is_unsat() {
            return Err(());
        }

        self.status = ConstrStatus::Processing;

        while let Some(constr_id) = self.unprocessed.pop() {
            if self.reduce(sema, diag, constr_id).is_err() {
                self.status = ConstrStatus::Unsat;

                return Err(());
            }
        }

        self.status = ConstrStatus::Sat;

        Ok(())
    }

    fn report_constr_violation(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        constr_id: ConstrId,
    ) {
        todo!()
    }

    fn reduce(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        constr_id: ConstrId,
    ) -> Result {
        let constr = &self.constrs[constr_id];

        match constr.kind {
            ConstrKind::Eq(lhs, rhs) => self.reduce_eq(sema, diag, constr_id, lhs, rhs),
            ConstrKind::Sub(lhs, rhs) => self.reduce_sub(sema, diag, constr_id, lhs, rhs),
            ConstrKind::Coerce(lhs, rhs) => self.reduce_coerce(sema, diag, constr_id, lhs, rhs),
        }
    }

    fn reduce_eq(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        constr_id: ConstrId,
        lhs: TyId,
        rhs: TyId,
    ) -> Result {
        let l = &sema.tyck.tys[lhs];
        let r = &sema.tyck.tys[rhs];

        match (l, r) {
            (&Ty::Var(l), _) => {
                self.add_var_bound(l, VarBound::Eq(rhs), VarBoundProvenance::Constr(constr_id))
            }

            (_, &Ty::Var(r)) => {
                self.add_var_bound(r, VarBound::Eq(lhs), VarBoundProvenance::Constr(constr_id))
            }

            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            (Ty::Ctor(l), Ty::Ctor(r)) => {
                if l.ctor != r.ctor {
                    self.report_constr_violation(sema, diag, constr_id);

                    return Err(());
                }

                for (lhs_arg, rhs_arg) in iter::zip(l.args.clone(), r.args.clone()) {
                    self.add(
                        sema,
                        diag,
                        Constr {
                            provenance: ConstrProvenance::Constr(constr_id),
                            kind: ConstrKind::Eq(lhs_arg, rhs_arg),
                        },
                    )?;
                }

                Ok(())
            }

            (Ty::Null, Ty::Null) => Ok(()),

            (Ty::Ctor(_) | Ty::Null, _) => {
                self.report_constr_violation(sema, diag, constr_id);

                Err(())
            }
        }
    }

    fn reduce_sub(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        constr_id: ConstrId,
        lhs: TyId,
        rhs: TyId,
    ) -> Result {
        let l = &sema.tyck.tys[lhs];
        let r = &sema.tyck.tys[rhs];

        match (l, r) {
            (&Ty::Var(l), _) => self.add_var_bound(
                l,
                VarBound::Upper(rhs),
                VarBoundProvenance::Constr(constr_id),
            ),

            (_, &Ty::Var(r)) => self.add_var_bound(
                r,
                VarBound::Upper(lhs),
                VarBoundProvenance::Constr(constr_id),
            ),

            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            (Ty::Ctor(l), Ty::Ctor(r)) => {
                // TODO: refine the subtyping relation.

                if l.ctor != r.ctor {
                    let bl = sema.name_res.defs[l.ctor].kind.as_builtin_ctor();
                    let br = sema.name_res.defs[r.ctor].kind.as_builtin_ctor();

                    // consider built-in types.
                    match (bl, br) {
                        (_, Some(BuiltinTyCtor::Any)) => return Ok(()),
                        (Some(BuiltinTyCtor::Nothing), _) => return Ok(()),

                        // apart from the two cases above, built-in types are never related to other
                        // types by subtyping unless their constructors are the same.
                        (Some(_), _) | (_, Some(_)) => {
                            self.report_constr_violation(sema, diag, constr_id);

                            return Err(());
                        }

                        _ => {}
                    }

                    // determinine the subtyping relationship between two different user-defined types.
                    // TODO: is there such in the first place?
                    self.report_constr_violation(sema, diag, constr_id);

                    return Err(());
                }

                // the two types have the same type constructor. this is now a question of variance.
                let ctor = l.ctor;
                let variances = sema.tyck.ctor_variances[ctor].clone();

                for (variance, (l_arg, r_arg)) in
                    iter::zip(variances, iter::zip(l.args.clone(), r.args.clone()))
                {
                    let kind = match variance {
                        Variance::Covariant => ConstrKind::Sub(l_arg, r_arg),
                        Variance::Contravariant => ConstrKind::Sub(r_arg, l_arg),
                        Variance::Invariant => ConstrKind::Eq(l_arg, r_arg),
                    };

                    self.add(
                        sema,
                        diag,
                        Constr {
                            provenance: ConstrProvenance::Constr(constr_id),
                            kind,
                        },
                    )?;
                }

                Ok(())
            }

            (Ty::Null, Ty::Null) => Ok(()),

            (Ty::Ctor(_) | Ty::Null, _) => {
                self.report_constr_violation(sema, diag, constr_id);

                Err(())
            }
        }
    }

    fn reduce_coerce(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        constr_id: ConstrId,
        lhs: TyId,
        rhs: TyId,
    ) -> Result {
        todo!()
    }

    fn add_var_bound(
        &mut self,
        idx: usize,
        bound: VarBound,
        provenance: VarBoundProvenance,
    ) -> Result {
        todo!()
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
    /// The left type equals the right type.
    ///
    /// Note that this requires the two types to be fully identical, and is a stronger requirement
    /// than type equivalence (wherein lhs <: rhs and rhs <: lhs).
    Eq(TyId, TyId),

    /// The left type is a subtype of the right type.
    ///
    /// Subsumes Eq.
    Sub(TyId, TyId),

    /// The left type is coercible to the right type.
    ///
    /// Subsumes Sub.
    Coerce(TyId, TyId),
}

#[derive(Debug, Clone, Default)]
pub struct BoundSet {
    vars: Vec<VarConstr>,
}

impl BoundSet {
    pub fn var(&self, idx: usize) -> &VarConstr {
        if idx >= self.vars.len() {
            static DEFAULT: LazyLock<VarConstr> = LazyLock::new(Default::default);

            &DEFAULT
        } else {
            &self.vars[idx]
        }
    }

    pub fn var_mut(&mut self, idx: usize) -> &mut VarConstr {
        if idx >= self.vars.len() {
            self.vars.resize_with(idx, Default::default);
        }

        &mut self.vars[idx]
    }
}

#[derive(Debug, Clone)]
pub enum VarProvenance {
    /// The type of a variable.
    Var(DefId),

    /// The type of an aggregate element.
    Element { of: ExprId },
}

#[derive(Debug, Clone)]
pub enum VarBoundProvenance {
    /// Arising from to a constraint reduction.
    Constr(ConstrId),
}

#[derive(Debug, Default, Clone)]
pub struct VarConstr {
    /// Lower bounds.
    ///
    /// Constrain the variable to be a supertype of the union of these types.
    pub lower: SparseSecondaryMap<TyId, VarBoundProvenance>,

    /// Upper bounds.
    ///
    /// Constrain the variable to be a subtype of the intersection of these types.
    pub upper: SparseSecondaryMap<TyId, VarBoundProvenance>,

    /// Equality bounds.
    pub eq: SparseSecondaryMap<TyId, VarBoundProvenance>,

    /// Instantiation with a proper type.
    pub inst: Option<TyId>,

    unprocessed: Vec<(VarBound, VarBoundProvenance)>,
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    pub fn constr_coerce(&mut self, lhs: TyId, rhs: TyId, provenance: ConstrProvenance) {
        self.result = self.result.or(self.constrs.add(
            self.sema,
            self.diag,
            Constr {
                provenance,
                kind: ConstrKind::Coerce(lhs, rhs),
            },
        ));
    }

    pub fn constr_sub(&mut self, lhs: TyId, rhs: TyId, provenance: ConstrProvenance) {
        self.result = self.result.or(self.constrs.add(
            self.sema,
            self.diag,
            Constr {
                provenance,
                kind: ConstrKind::Sub(lhs, rhs),
            },
        ));
    }

    pub fn constr_eq(&mut self, lhs: TyId, rhs: TyId, provenance: ConstrProvenance) {
        self.result = self.result.or(self.constrs.add(
            self.sema,
            self.diag,
            Constr {
                provenance,
                kind: ConstrKind::Eq(lhs, rhs),
            },
        ));
    }

    pub fn fresh_var(&mut self, provenance: VarProvenance) -> TyId {
        let idx = self.sema.tyck.var_provenances.len();
        self.sema.tyck.var_provenances.push(provenance);
        let ty_id = self.sema.tyck.add_ty(Ty::Var(idx));

        ty_id
    }
}
