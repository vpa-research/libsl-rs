//! Type constraint solving.

use std::cell::RefCell;
use std::collections::HashMap;
use std::{iter, mem};
use std::sync::LazyLock;

use bit_set::BitSet;
use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap, new_key_type};

use crate::ast::Variance;
use crate::diag::DiagCtx;
use crate::sema::def::DefId;
use crate::sema::ty::{BuiltinTyCtor, ConstructedTy, Ty, TyId};
use crate::sema::tyck::{Pass, TyCk};
use crate::sema::{Result, Sema};
use crate::{AccessId, ExprId};

new_key_type! {
    pub struct ConstrId;
}

#[derive(Debug, Clone, Default)]
enum Status {
    #[default]
    Sat,

    Processing,

    Unsat,
}

impl Status {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubtypeBoundKind {
    Lower,
    Upper,
}

impl SubtypeBoundKind {
    fn opposite(self) -> Self {
        match self {
            Self::Lower => Self::Upper,
            Self::Upper => Self::Lower,
        }
    }

    fn order_subtype(self, ty_id: TyId, bound_ty_id: TyId) -> (TyId, TyId) {
        match self {
            Self::Lower => (bound_ty_id, ty_id),
            Self::Upper => (ty_id, bound_ty_id),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TyUnionFind {
    parents: RefCell<SecondaryMap<TyId, TyId>>,
}

impl TyUnionFind {
    pub fn repr(&self, mut ty_id: TyId) -> TyId {
        let mut parents = self.parents.borrow_mut();
        parents.entry(ty_id).unwrap().or_insert(ty_id);

        while parents[ty_id] != ty_id {
            let grandparent = parents[parents[ty_id]];
            parents[ty_id] = grandparent;
            ty_id = grandparent;
        }

        ty_id
    }

    fn union(&self, lhs: TyId, rhs: TyId) {
        let lhs = self.repr(lhs);
        let rhs = self.repr(rhs);

        if lhs == rhs {
            return;
        }

        self.parents.borrow_mut()[lhs] = rhs;
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstrSet {
    constrs: SlotMap<ConstrId, Constr>,
    constr_dedup: HashMap<ConstrKind, ConstrId>,
    unprocessed: Vec<ConstrId>,
    pub bounds: BoundSet,
    status: Status,

    uf: TyUnionFind,

    // quotient of TyCk.preds over the congruence induced by uf.
    // the keys are congruence class representatives.
    // does not contain duplicates.
    preds: SecondaryMap<TyId, Vec<TyId>>,

    last_registered_ty_idx: usize,
}

impl ConstrSet {
    pub fn repr(&self, ty_id: TyId) -> TyId {
        self.uf.repr(ty_id)
    }

    fn union(&mut self, sema: &Sema<'_>, lhs_ty_id: TyId, rhs_ty_id: TyId) -> TyId {
        let lhs_ty_id = self.repr(lhs_ty_id);
        let rhs_ty_id = self.repr(rhs_ty_id);

        // avoid putting a variable at the top.
        if sema.tyck.tys[lhs_ty_id].is_var() && !sema.tyck.tys[rhs_ty_id].is_var() {
            return self.union(sema, rhs_ty_id, lhs_ty_id);
        }

        self.uf.union(lhs_ty_id, rhs_ty_id);

        let rhs_preds = mem::take(self.preds_mut(sema, rhs_ty_id));
        let preds = self.preds_mut(sema, lhs_ty_id);
        preds.extend(rhs_preds);
        preds.sort();
        preds.dedup();

        lhs_ty_id
    }

    fn are_congruent(&self, sema: &Sema<'_>, lhs_ty_id: TyId, rhs_ty_id: TyId) -> bool {
        let lhs = &sema.tyck.tys[lhs_ty_id];
        let rhs = &sema.tyck.tys[rhs_ty_id];

        match (lhs, rhs) {
            (Ty::Error, Ty::Error) => true,

            (Ty::Ctor(l), Ty::Ctor(r)) => {
                l.ctor == r.ctor
                    && iter::zip(&l.args, &r.args).all(|(&l, &r)| self.repr(l) == self.repr(r))
            }

            (Ty::Var(l), Ty::Var(r)) => l == r,

            (Ty::Null, Ty::Null) => true,

            (Ty::Error | Ty::Ctor(_) | Ty::Var(_) | Ty::Null, _) => false,
        }
    }

    pub fn merge(&mut self, sema: &mut Sema<'_>, lhs_ty_id: TyId, rhs_ty_id: TyId) {
        let lhs_ty_id = self.normalize(sema, lhs_ty_id, true);
        let rhs_ty_id = self.normalize(sema, rhs_ty_id, true);
        let lhs_preds = self.preds(sema, lhs_ty_id).to_vec();
        let rhs_preds = self.preds(sema, rhs_ty_id).to_vec();
        self.union(sema, lhs_ty_id, rhs_ty_id);

        for &l in &lhs_preds {
            for &r in &rhs_preds {
                if self.repr(l) == self.repr(r) {
                    continue;
                }

                if self.are_congruent(sema, l, r) {
                    self.merge(sema, l, r);
                }
            }
        }
    }

    fn preds<'a>(&'a self, sema: &'a Sema<'_>, ty_id: TyId) -> &'a [TyId] {
        self.preds
            .get(ty_id)
            .map(|preds| &preds[..])
            .unwrap_or_else(|| &sema.tyck.ty_preds[ty_id])
    }

    fn preds_mut(&mut self, sema: &Sema<'_>, ty_id: TyId) -> &mut Vec<TyId> {
        self.preds.entry(ty_id).unwrap().or_insert_with(|| {
            let mut result = sema.tyck.ty_preds[ty_id].clone();
            result.sort();
            result.dedup();

            result
        })
    }

    pub fn add(&mut self, sema: &mut Sema<'_>, diag: &mut impl DiagCtx, constr: Constr) -> Result {
        use std::collections::hash_map::Entry;

        if self.status.is_unsat() {
            return Err(());
        }

        let Entry::Vacant(entry) = self.constr_dedup.entry(constr.kind.clone()) else {
            return Ok(());
        };

        let id = self.constrs.insert(constr);
        entry.insert(id);
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

        self.status = Status::Processing;

        while let Some(&ty_id) = sema.tyck.ty_vec.get(self.last_registered_ty_idx) {
            self.normalize(sema, ty_id, false);
            self.last_registered_ty_idx += 1;
        }

        while let Some(constr_id) = self.unprocessed.pop() {
            if self.reduce(sema, diag, constr_id).is_err() {
                self.status = Status::Unsat;

                return Err(());
            }
        }

        self.status = Status::Sat;

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

    fn normalize(&mut self, sema: &mut Sema<'_>, ty_id: TyId, force: bool) -> TyId {
        if !force && self.uf.parents.borrow().contains_key(ty_id) {
            return self.repr(ty_id);
        }

        let ty_id = self.repr(ty_id);
        let ty = &sema.tyck.tys[ty_id];

        let normalized = match ty {
            Ty::Error => Ty::Error,

            Ty::Ctor(t) => Ty::Ctor(ConstructedTy {
                ctor: t.ctor,
                args: t
                    .args
                    .clone()
                    .into_iter()
                    .map(|arg| self.normalize(sema, arg, false))
                    .collect(),
            }),

            &Ty::Var(idx) => Ty::Var(idx),

            Ty::Null => Ty::Null,
        };

        let normalized_ty_id = sema.tyck.add_ty(normalized);

        self.union(sema, ty_id, normalized_ty_id)
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
        let lhs = self.repr(lhs);
        let rhs = self.repr(rhs);

        self.merge(sema, lhs, rhs);

        let l = &sema.tyck.tys[lhs];
        let r = &sema.tyck.tys[rhs];

        match (l, r) {
            (&Ty::Var(l), _) => self.add_var_bound(
                sema,
                diag,
                l,
                VarBound::Eq(rhs),
                VarBoundProvenance::Constr(constr_id),
            ),

            (_, &Ty::Var(r)) => self.add_var_bound(
                sema,
                diag,
                r,
                VarBound::Eq(lhs),
                VarBoundProvenance::Constr(constr_id),
            ),

            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            (Ty::Ctor(l), Ty::Ctor(r)) => {
                if l.ctor != r.ctor {
                    self.report_constr_violation(sema, diag, constr_id);

                    return Err(());
                }

                for (lhs_arg, rhs_arg) in iter::zip(l.args.clone(), r.args.clone()) {
                    let lhs_arg = self.repr(lhs_arg);
                    let rhs_arg = self.repr(rhs_arg);

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

        if rhs == sema.tyck.builtin.any {
            return Ok(());
        }

        if lhs == sema.tyck.builtin.nothing {
            return Ok(());
        }

        match (l, r) {
            (&Ty::Var(l), _) => self.add_var_bound(
                sema,
                diag,
                l,
                VarBound::Upper(rhs),
                VarBoundProvenance::Constr(constr_id),
            ),

            (_, &Ty::Var(r)) => self.add_var_bound(
                sema,
                diag,
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
                        // built-in types are never related to other types by subtyping unless their
                        // constructors are the same.
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
        let l = &sema.tyck.tys[lhs];
        let r = &sema.tyck.tys[rhs];

        match (l, r) {
            (Ty::Ctor(l), Ty::Ctor(r)) => {
                if l.ctor != r.ctor {
                    let bl = sema.name_res.defs[l.ctor].kind.as_builtin_ctor();
                    let br = sema.name_res.defs[r.ctor].kind.as_builtin_ctor();

                    match (bl, br) {
                        // can extend the integer width as long as the signedness is preserved.
                        (Some(BuiltinTyCtor::Int(l_int)), Some(BuiltinTyCtor::Int(r_int)))
                            if l_int.signed == r_int.signed && l_int.width <= r_int.width =>
                        {
                            return Ok(());
                        }

                        // can extend the float width.
                        (
                            Some(BuiltinTyCtor::Float(l_float)),
                            Some(BuiltinTyCtor::Float(r_float)),
                        ) if l_float.width() <= r_float.width() => {
                            return Ok(());
                        }

                        _ => {}
                    }
                }
            }

            _ => {}
        }

        // not a known coercion — require subtyping.
        self.reduce_sub(sema, diag, constr_id, lhs, rhs)
    }

    fn add_var_bound(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        bound: VarBound,
        provenance: VarBoundProvenance,
    ) -> Result {
        let var = self.bounds.var_mut(idx);

        if var.status.is_unsat() {
            return Err(());
        }

        var.unprocessed.push((bound, provenance));

        if var.status.is_processing() {
            Ok(())
        } else {
            self.process_var_bounds(sema, diag, idx)
        }
    }

    fn process_var_bounds(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
    ) -> Result {
        let mut var = self.bounds.var_mut(idx);

        assert!(!var.status.is_processing());

        if var.status.is_unsat() {
            return Err(());
        }

        var.status = Status::Processing;

        while let Some((bound, provenance)) = var.unprocessed.pop() {
            let result = self.incorporate(sema, diag, idx, bound, provenance);
            var = self.bounds.var_mut(idx);

            if result.is_err() {
                var.status = Status::Unsat;

                return Err(());
            }
        }

        var.status = Status::Sat;

        Ok(())
    }

    fn update_bounds(&mut self, idx: usize) {
        let var = self.bounds.var_mut(idx);

        for bounds in [&mut var.lower, &mut var.upper] {
            let mut to_update = vec![];

            for ty_id in bounds.keys() {
                let repr = self.uf.repr(ty_id);

                if repr != ty_id {
                    to_update.push((ty_id, repr));
                }
            }

            for (from, to) in to_update {
                let provenance = bounds.remove(from).unwrap();
                bounds.entry(to).unwrap().or_insert(provenance);
            }
        }

        if let Some((ty_id, _)) = &mut var.eq {
            *ty_id = self.uf.repr(*ty_id);
        }
    }

    fn incorporate(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        bound: VarBound,
        provenance: VarBoundProvenance,
    ) -> Result {
        match bound {
            VarBound::Lower(ty_id) => self.incorporate_lower(sema, diag, idx, ty_id, provenance),
            VarBound::Upper(ty_id) => self.incorporate_upper(sema, diag, idx, ty_id, provenance),
            VarBound::Eq(ty_id) => self.incorporate_eq(sema, diag, idx, ty_id, provenance, true),
        }
    }

    fn incorporate_subtype(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        ty_id: TyId,
        kind: SubtypeBoundKind,
        provenance: VarBoundProvenance,
    ) -> Result {
        use slotmap::sparse_secondary::Entry;

        let ty_id = self.repr(ty_id);
        self.update_bounds(idx);

        let var_ty_id = sema.tyck.add_ty(Ty::Var(idx));

        // α <: α: true by reflexivity.
        if ty_id == var_ty_id {
            return Ok(());
        }

        let var = self.bounds.var_mut(idx);

        // check if we already have such a bound.
        let Entry::Vacant(entry) = var.subtype_bounds_mut(kind).entry(ty_id).unwrap() else {
            return Ok(());
        };

        entry.insert(provenance.clone());

        // check for antisymmetry.
        if var.subtype_bounds(kind.opposite()).contains_key(ty_id) {
            return self.incorporate_eq(
                sema,
                diag,
                idx,
                ty_id,
                VarBoundProvenance::Antisymmetry,
                true,
            );
        }

        // ensure the new bound is consistent with the opposite bounds.
        let bounds = var
            .subtype_bounds(kind.opposite())
            .keys()
            .collect::<Vec<_>>();

        for &bound_ty_id in &bounds {
            let (lower_ty_id, upper_ty_id) = kind.opposite().order_subtype(ty_id, bound_ty_id);

            self.add(
                sema,
                diag,
                Constr {
                    provenance: ConstrProvenance::SubBound { idx },
                    kind: ConstrKind::Sub(lower_ty_id, upper_ty_id),
                },
            )?;
        }

        // if the bound is a variable, process it as well.
        if let Ty::Var(v) = sema.tyck.tys[ty_id] {
            let var_ty_id = sema.tyck.add_ty(Ty::Var(idx));

            return match kind {
                SubtypeBoundKind::Lower => {
                    self.incorporate_upper(sema, diag, v, var_ty_id, provenance)
                }

                SubtypeBoundKind::Upper => {
                    self.incorporate_lower(sema, diag, v, var_ty_id, provenance)
                }
            };
        }

        Ok(())
    }

    fn incorporate_lower(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        ty_id: TyId,
        provenance: VarBoundProvenance,
    ) -> Result {
        self.incorporate_subtype(sema, diag, idx, ty_id, SubtypeBoundKind::Lower, provenance)
    }

    fn incorporate_upper(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        ty_id: TyId,
        provenance: VarBoundProvenance,
    ) -> Result {
        self.incorporate_subtype(sema, diag, idx, ty_id, SubtypeBoundKind::Upper, provenance)
    }

    fn incorporate_eq(
        &mut self,
        sema: &mut Sema<'_>,
        diag: &mut impl DiagCtx,
        idx: usize,
        ty_id: TyId,
        provenance: VarBoundProvenance,
        apply_symmetry: bool,
    ) -> Result {
        let ty_id = self.repr(ty_id);
        self.update_bounds(idx);

        let var_ty_id = sema.tyck.add_ty(Ty::Var(idx));

        // α = α: true by reflexivity.
        if ty_id == var_ty_id {
            return Ok(());
        }

        let var = self.bounds.var_mut(idx);

        // the type must equal an existing eq bound (transitivity).
        if let Some((eq, _)) = var.eq {
            self.add(
                sema,
                diag,
                Constr {
                    provenance: ConstrProvenance::SubBound { idx },
                    kind: ConstrKind::Eq(eq, ty_id),
                },
            )?;
        } else {
            var.eq = Some((ty_id, provenance.clone()));
        }

        // the type must satisfy lower/upper bounds.
        let var = self.bounds.var(idx);
        let lower_bounds = var.lower.keys().collect::<Vec<_>>();
        let upper_bounds = var.upper.keys().collect::<Vec<_>>();

        for lower_ty_id in lower_bounds {
            self.add(
                sema,
                diag,
                Constr {
                    provenance: ConstrProvenance::EqBound { idx },
                    kind: ConstrKind::Sub(lower_ty_id, ty_id),
                },
            )?;
        }

        for upper_ty_id in upper_bounds {
            self.add(
                sema,
                diag,
                Constr {
                    provenance: ConstrProvenance::EqBound { idx },
                    kind: ConstrKind::Sub(ty_id, upper_ty_id),
                },
            )?;
        }

        // if the type is a variable, apply symmetry.
        if apply_symmetry && let Ty::Var(v) = sema.tyck.tys[ty_id] {
            return self.incorporate_eq(sema, diag, v, var_ty_id, provenance, false);
        }

        Ok(())
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

    /// Ensures a bound consistency.
    SubBound { idx: usize },

    /// Ensures that an equality bound satisfies subtyping bounds.
    EqBound { idx: usize },
}

#[derive(Debug, Clone)]
pub struct Constr {
    pub provenance: ConstrProvenance,
    pub kind: ConstrKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn is_free(&self, tyck: &TyCk, ty_id: TyId) -> bool {
        if let Ty::Var(idx) = tyck.tys[ty_id]
            && let Some((inst, _)) = self.var(idx).eq
        {
            self.is_free(tyck, inst)
        } else {
            tyck.var_occurrences[ty_id]
                .iter()
                .any(|&var| self.is_free(tyck, var))
        }
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

    /// Arising from the antisymmetry of subtyping.
    Antisymmetry,
}

// Invariants:
// 1. for all l ∈ .lower and u ∈ .upper, l <: u.
// 2. if a variable in a bound has an instantiation, it holds after substitution.
// 3. if α = β, their bounds are the same.
// 4. if α <: β, α.lower ⊆ β.lower and β.upper ⊆ α.upper.
// 5. if α <: β, β ∈ α.upper and α ∈ β.lower.
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

    /// An equality bound, if any.
    pub eq: Option<(TyId, VarBoundProvenance)>,

    /// Indices of variables whose bounds mention this variable.
    used_by: BitSet,

    unprocessed: Vec<(VarBound, VarBoundProvenance)>,
    status: Status,
}

impl VarConstr {
    fn subtype_bounds(
        &self,
        kind: SubtypeBoundKind,
    ) -> &SparseSecondaryMap<TyId, VarBoundProvenance> {
        match kind {
            SubtypeBoundKind::Lower => &self.lower,
            SubtypeBoundKind::Upper => &self.upper,
        }
    }

    fn subtype_bounds_mut(
        &mut self,
        kind: SubtypeBoundKind,
    ) -> &mut SparseSecondaryMap<TyId, VarBoundProvenance> {
        match kind {
            SubtypeBoundKind::Lower => &mut self.lower,
            SubtypeBoundKind::Upper => &mut self.upper,
        }
    }
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
