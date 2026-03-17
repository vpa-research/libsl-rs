//! Overload resolution.

use std::cmp::Ordering;
use std::fmt::Write;
use std::iter;

use crate::diag::{Diag, DiagCtx, DummyDiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::DefId;
use crate::sema::resolve::ScopeKind;
use crate::sema::ty::{Ty, TyId};
use crate::sema::tyck::constraints::{Constr, ConstrKind, ConstrProvenance};
use crate::sema::tyck::{Pass, ReplaceTyArgs};
use crate::sema::{Result, Sema};
use crate::{ExprId, WithLibSl};

use super::FnSig;

#[derive(Debug, Clone)]
pub enum Receiver {
    None,
    Implicit(TyId),
    Explicit(TyId),
}

pub trait FnSigProvider {
    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig;

    fn applicability_constr_provenance(&self) -> ConstrProvenance;
}

impl<T: FnSigProvider> FnSigProvider for &'_ T {
    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig {
        (*self).fn_sig(sema)
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        (*self).applicability_constr_provenance()
    }
}

struct DefFnSigProvider(DefId);

impl FnSigProvider for DefFnSigProvider {
    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig {
        &sema.tyck.sigs[self.0]
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        ConstrProvenance::Fn(self.0)
    }
}

pub trait OverloadDiagProvider<F: FnSigProvider> {
    fn empty_candidate_set(&self, sema: &Sema<'_>) -> Diag;

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&F]) -> Diag;
}

struct CallOverloadDiagProvider<'a> {
    name: &'a str,
    loc: &'a Loc,
}

impl OverloadDiagProvider<DefFnSigProvider> for CallOverloadDiagProvider<'_> {
    fn empty_candidate_set(&self, _sema: &Sema<'_>) -> Diag {
        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!("no function named `{}` found", self.name))
            .with_label(Label::primary(self.loc.clone()))
            .build()
    }

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&DefFnSigProvider]) -> Diag {
        let mut possible_candidates = "the following candidates are possible:".to_owned();

        for candidate in ambiguities {
            let _ = write!(
                possible_candidates,
                "\n  - {} defined at {}",
                sema.format_def_signature(candidate.0),
                sema.name_res.defs[candidate.0].loc.with_libsl(sema.libsl),
            );
        }

        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!(
                "call to {} is ambiguous: found {} possible candidates",
                self.name,
                ambiguities.len(),
            ))
            .with_label(
                Label::primary(self.loc.clone())
                    .with_msg("cannot determine which function this refers to"),
            )
            .with_note(possible_candidates)
            .build()
    }
}

struct SelectionCriteria {
    concrete_only: bool,
}

impl SelectionCriteria {
    fn should_consider(&self, sema: &Sema<'_>, f: &impl FnSigProvider) -> bool {
        if self.concrete_only && !f.fn_sig(sema).generics.is_empty() {
            return false;
        }

        true
    }

    fn strengthen(&mut self, sema: &Sema<'_>, candidates: &[impl FnSigProvider]) -> bool {
        if !self.concrete_only && self.strengthen_concrete(sema, candidates) {
            return true;
        }

        false
    }

    fn strengthen_concrete(&mut self, sema: &Sema<'_>, candidates: &[impl FnSigProvider]) -> bool {
        let mut has_concrete = false;
        let mut has_parameterized = false;

        for candidate in candidates {
            if candidate.fn_sig(sema).generics.is_empty() {
                has_concrete = true;
            } else {
                has_parameterized = true;
            }

            if has_concrete && has_parameterized {
                self.concrete_only = true;

                return true;
            }
        }

        false
    }
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    pub(super) fn resolve_callee(
        &mut self,
        loc: &Loc,
        expr_id: ExprId,
        recv: &Receiver,
        name: &str,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        match recv {
            Receiver::None | Receiver::Implicit(_) => {
                self.resolve_plain_name_callee(loc, expr_id, recv, name, args, ty_args)
            }

            Receiver::Explicit(ty_id) => {
                self.resolve_explicit_recv_callee(loc, name, *ty_id, args, ty_args)
            }
        }
    }

    fn find_method_candidates(
        &mut self,
        candidates: &mut Vec<DefFnSigProvider>,
        def_id: DefId,
        name: &str,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) {
        let member_scope_id = self.sema.name_res.def_member_scopes[def_id];

        if let Some(overloads) = self.sema.name_res.scopes[member_scope_id]
            .functions
            .get(name)
        {
            candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                let provider = DefFnSigProvider(def_id);

                self.is_function_applicable(&provider, recv, args, ty_args)
                    .then_some(provider)
            }));
        }
    }

    fn resolve_plain_name_callee(
        &mut self,
        loc: &Loc,
        expr_id: ExprId,
        recv: &Receiver,
        name: &str,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        let mut next_scope_id = Some(self.sema.name_res.exprs[expr_id].scope_id);

        let mut candidates = vec![];

        while let Some(scope_id) = next_scope_id {
            let scope = &self.sema.name_res.scopes[scope_id];
            next_scope_id = scope.parent;

            match &scope.kind {
                ScopeKind::Dummy => unreachable!(),

                ScopeKind::Params(_) | ScopeKind::Block { .. } => {
                    // regular scopes never define functions.
                }

                ScopeKind::Prelude | ScopeKind::Import(_) | ScopeKind::File(_) => {
                    if let Some(overloads) = scope.functions.get(name) {
                        candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                            let provider = DefFnSigProvider(def_id);

                            self.is_function_applicable(&provider, recv, args, ty_args)
                                .then_some(provider)
                        }));
                    }
                }

                ScopeKind::SemanticTyEnum(_) => {
                    // enumerated semantic types do not define functions.
                }

                ScopeKind::Struct(def_id) | ScopeKind::Automaton(def_id) => {
                    self.find_method_candidates(
                        &mut candidates,
                        *def_id,
                        name,
                        recv,
                        args,
                        ty_args,
                    );
                }

                ScopeKind::Enum(_) => {
                    // enums never define functions.
                }
            }

            if !candidates.is_empty() {
                break;
            }
        }

        let diag_provider = CallOverloadDiagProvider { loc, name };

        self.select_overload(&candidates, &diag_provider)
            .map(|candidate| candidate.0)
    }

    fn resolve_explicit_recv_callee(
        &mut self,
        loc: &Loc,
        name: &str,
        recv_ty_id: TyId,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        let recv = Receiver::Explicit(recv_ty_id);
        let mut candidates = vec![];

        match &self.sema.tyck.tys[recv_ty_id] {
            Ty::Error => unreachable!(),

            Ty::Ctor(t) => {
                self.find_method_candidates(&mut candidates, t.ctor, name, &recv, args, ty_args);
            }

            Ty::Param(_) => todo!(),
            Ty::Var(_) => todo!(),
            Ty::Null => todo!(),
            Ty::Union(_) => todo!(),
        }

        let diag_provider = CallOverloadDiagProvider { loc, name };

        self.select_overload(&candidates, &diag_provider)
            .map(|candidate| candidate.0)
    }

    pub fn is_function_applicable(
        &mut self,
        candidate: &impl FnSigProvider,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> bool {
        (|| -> Result<()> {
            let mut constr = self.constrs.clone();
            let sig = candidate.fn_sig(self.sema).clone();

            if ty_args.len() > sig.generics.len() || args.len() != sig.params.len() {
                return Err(());
            }

            let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &Loc::Synthetic);

            for (&param, &arg) in iter::zip(&sig.generics, ty_args) {
                constr.add(
                    self.sema,
                    &mut DummyDiagCtx,
                    Constr {
                        kind: ConstrKind::Eq(arg, ty_param_map[param]),
                        provenance: candidate.applicability_constr_provenance(),
                    },
                )?;
            }

            match (recv, sig.recv) {
                (Receiver::None, None) => {}

                (Receiver::Implicit(_), None) => {}

                (Receiver::Implicit(ty_id) | Receiver::Explicit(ty_id), Some(recv)) => {
                    let expected = self.make_recv_ty(recv, ReplaceTyArgs::Yes(&Loc::Synthetic));

                    constr.add(
                        self.sema,
                        &mut DummyDiagCtx,
                        Constr {
                            kind: ConstrKind::Sub(*ty_id, expected),
                            provenance: candidate.applicability_constr_provenance(),
                        },
                    )?;
                }

                _ => return Err(()),
            }

            for (&param, &arg) in iter::zip(&sig.params, args) {
                let param = self.sema.tyck.subst(param, &ty_param_map);

                constr.add(
                    self.sema,
                    &mut DummyDiagCtx,
                    Constr {
                        kind: ConstrKind::Coerce(arg, param),
                        provenance: candidate.applicability_constr_provenance(),
                    },
                )?;
            }

            Ok(())
        })()
        .is_ok()
    }

    fn is_lhs_more_specific(&mut self, lhs: &impl FnSigProvider, rhs: &impl FnSigProvider) -> bool {
        if lhs.fn_sig(self.sema).params.len() != rhs.fn_sig(self.sema).params.len() {
            return false;
        }

        let ty_param_map = lhs
            .fn_sig(self.sema)
            .generics
            .clone()
            .into_iter()
            .map(|generic| (generic, self.sema.tyck.clone_param(generic)))
            .collect();

        let args = lhs
            .fn_sig(self.sema)
            .params
            .clone()
            .into_iter()
            .map(|param| self.sema.tyck.subst(param, &ty_param_map))
            .collect::<Vec<_>>();

        let recv = match lhs.fn_sig(self.sema).recv {
            Some(_) => unimplemented!(),
            None => Receiver::None,
        };

        self.is_function_applicable(rhs, &recv, &args, &[])
    }

    fn compare_overloads(
        &mut self,
        lhs: &impl FnSigProvider,
        rhs: &impl FnSigProvider,
    ) -> Option<Ordering> {
        match (
            self.is_lhs_more_specific(lhs, rhs),
            self.is_lhs_more_specific(rhs, lhs),
        ) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }

    pub fn select_overload<'a, F: FnSigProvider>(
        &mut self,
        candidates: &'a [F],
        diag_provider: &impl OverloadDiagProvider<F>,
    ) -> Result<&'a F> {
        if candidates.is_empty() {
            self.result = Err(());
            self.diag.emit(diag_provider.empty_candidate_set(self.sema));

            return Err(());
        }

        let mut criteria = SelectionCriteria {
            concrete_only: false,
        };

        let mut best;
        let mut ambiguities = vec![];

        loop {
            best = candidates
                .iter()
                .find(|&candidate| criteria.should_consider(self.sema, candidate))
                .unwrap();
            ambiguities.clear();

            for candidate in candidates.iter().skip(1) {
                if !criteria.should_consider(self.sema, candidate) {
                    continue;
                }

                match self.compare_overloads(candidate, best) {
                    Some(Ordering::Less) => {
                        ambiguities.clear();
                        best = candidate;
                    }

                    Some(Ordering::Greater) => {}

                    None | Some(Ordering::Equal) => {
                        ambiguities.push(candidate);
                    }
                }
            }

            if !criteria.strengthen(self.sema, &ambiguities) {
                break;
            }
        }

        if !ambiguities.is_empty() {
            ambiguities.insert(0, best);
            self.result = Err(());
            self.diag
                .emit(diag_provider.ambiguity(self.sema, &ambiguities));

            return Err(());
        }

        Ok(best)
    }
}
