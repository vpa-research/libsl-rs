//! Overload resolution.

use std::cmp::Ordering;
use std::fmt::{self, Display, Write};
use std::iter;

use crate::diag::{Diag, DiagCtx, DummyDiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{DefFunction, DefId, FunctionKind};
use crate::sema::resolve::ScopeKind;
use crate::sema::ty::{Ty, TyId};
use crate::sema::tyck::constraints::{Constr, ConstrKind, ConstrProvenance};
use crate::sema::tyck::{Pass, ReplaceTyArgs};
use crate::sema::{Result, Sema};
use crate::util::format_sep_list;
use crate::{ExprId, WithLibSl, trace_enabled};

use super::FnSig;

#[derive(Debug, Clone)]
pub enum Receiver {
    None,
    Implicit(TyId),
    Explicit(TyId),
}

impl Receiver {
    pub fn is_some(&self) -> bool {
        !matches!(self, Self::None)
    }
}

#[derive(Debug, Default, Clone)]
pub struct ApplicabilityCriteria {
    pub proc_only: bool,
}

impl ApplicabilityCriteria {
    pub fn for_proc_call() -> Self {
        Self { proc_only: true }
    }
}

pub trait FnSigProvider {
    fn satisfies(&self, sema: &mut Sema<'_>, criteria: &ApplicabilityCriteria) -> bool;

    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig;

    fn applicability_constr_provenance(&self) -> ConstrProvenance;
}

impl<T: FnSigProvider> FnSigProvider for &'_ T {
    fn satisfies(&self, sema: &mut Sema<'_>, criteria: &ApplicabilityCriteria) -> bool {
        (*self).satisfies(sema, criteria)
    }

    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig {
        (*self).fn_sig(sema)
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        (*self).applicability_constr_provenance()
    }
}

struct DefFnSigProvider(DefId);

impl FnSigProvider for DefFnSigProvider {
    fn satisfies(&self, sema: &mut Sema<'_>, criteria: &ApplicabilityCriteria) -> bool {
        let &ApplicabilityCriteria { proc_only } = criteria;

        if proc_only {
            if !matches!(
                sema.name_res.def::<DefFunction>(self.0).kind,
                FunctionKind::Proc { .. }
            ) {
                return false;
            }
        }

        true
    }

    fn fn_sig<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnSig {
        &sema.tyck.sigs[self.0]
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        ConstrProvenance::Fn(self.0)
    }
}

pub trait OverloadDiagProvider<F: FnSigProvider> {
    fn empty_candidate_set<D: DiagCtx>(&self, pass: &Pass<'_, '_, D>) -> Diag;

    fn ambiguity<D: DiagCtx>(&self, pass: &Pass<'_, '_, D>, ambiguities: &[&F]) -> Diag;
}

struct CallOverloadDiagProvider<'a> {
    name: &'a str,
    loc: &'a Loc,
    recv: &'a Receiver,
    ty_args: &'a [TyId],
    args: &'a [TyId],
}

impl CallOverloadDiagProvider<'_> {
    fn display_call_sig<D: DiagCtx>(&self, pass: &Pass<'_, '_, D>) -> impl Display {
        let format_ty = |ty_id| pass.sema.format_ty(pass.repr(ty_id));

        fmt::from_fn(move |f| {
            match self.recv {
                Receiver::None => {}
                Receiver::Implicit(ty_id) => write!(f, "({}).", format_ty(*ty_id))?,
                Receiver::Explicit(ty_id) => write!(f, "{}.", format_ty(*ty_id))?,
            }

            write!(f, "{}", self.name)?;

            if !self.ty_args.is_empty() {
                write!(
                    f,
                    "<{}>",
                    format_sep_list(self.ty_args, |f, &ty_arg| write!(
                        f,
                        "{}",
                        format_ty(ty_arg),
                    ))
                )?;
            }

            write!(
                f,
                "({})",
                format_sep_list(self.args, |f, &arg| write!(f, "{}", format_ty(arg))),
            )?;

            Ok(())
        })
    }
}

impl OverloadDiagProvider<DefFnSigProvider> for CallOverloadDiagProvider<'_> {
    fn empty_candidate_set<D: DiagCtx>(&self, pass: &Pass<'_, '_, D>) -> Diag {
        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!(
                "no applicable function named `{}` found",
                self.name,
            ))
            .with_label(Label::primary(self.loc.clone()))
            .with_note(format!(
                "this call has signature {}",
                self.display_call_sig(pass),
            ))
            .build()
    }

    fn ambiguity<D: DiagCtx>(
        &self,
        pass: &Pass<'_, '_, D>,
        ambiguities: &[&DefFnSigProvider],
    ) -> Diag {
        let mut possible_candidates = "the following candidates are possible:".to_owned();

        for candidate in ambiguities {
            let _ = write!(
                possible_candidates,
                "\n- {} defined at {}",
                pass.sema.format_def_signature(candidate.0),
                pass.sema.name_res.defs[candidate.0]
                    .loc
                    .with_libsl(pass.sema.libsl),
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
            .with_note(format!(
                "this call has signature {}",
                self.display_call_sig(pass),
            ))
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
        criteria: &ApplicabilityCriteria,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) {
        let Some(&member_scope_id) = self.sema.name_res.def_member_scopes.get(def_id) else {
            return;
        };

        if recv.is_some()
            && let Some(&instance_scope_id) = self.sema.name_res.def_instance_scopes.get(def_id)
            && let Some(overloads) = self.sema.name_res.scopes[instance_scope_id]
                .functions
                .get(name)
        {
            candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                let def_id = self.sema.name_res.resolve_import(def_id);
                let provider = DefFnSigProvider(def_id);

                self.is_function_applicable(&provider, criteria, recv, args, ty_args)
                    .then_some(provider)
            }));
        }

        if let Some(overloads) = self.sema.name_res.scopes[member_scope_id]
            .functions
            .get(name)
        {
            candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                let def_id = self.sema.name_res.resolve_import(def_id);
                let provider = DefFnSigProvider(def_id);

                self.is_function_applicable(&provider, criteria, recv, args, ty_args)
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
        let mut candidates = vec![];
        let mut next_scope_id = Some(self.sema.name_res.exprs[expr_id].scope_id);
        let criteria = ApplicabilityCriteria::for_proc_call();

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
                            let def_id = self.sema.name_res.resolve_import(def_id);
                            let provider = DefFnSigProvider(def_id);

                            self.is_function_applicable(&provider, &criteria, recv, args, ty_args)
                                .then_some(provider)
                        }));
                    }
                }

                ScopeKind::Instance(def_id) | ScopeKind::Member(def_id) => {
                    self.find_method_candidates(
                        &mut candidates,
                        *def_id,
                        name,
                        &criteria,
                        recv,
                        args,
                        ty_args,
                    );
                }
            }

            if !candidates.is_empty() {
                break;
            }
        }

        let diag_provider = CallOverloadDiagProvider {
            loc,
            name,
            recv,
            ty_args,
            args,
        };

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
                self.find_method_candidates(
                    &mut candidates,
                    t.ctor,
                    name,
                    &ApplicabilityCriteria::for_proc_call(),
                    &recv,
                    args,
                    ty_args,
                );
            }

            Ty::Param(_) => {}
            Ty::Var(_) => {}
            Ty::Null => {}
            Ty::Union(_) => {}
        }

        let diag_provider = CallOverloadDiagProvider {
            loc,
            name,
            recv: &recv,
            ty_args,
            args,
        };

        self.select_overload(&candidates, &diag_provider)
            .map(|candidate| candidate.0)
    }

    pub fn is_function_applicable(
        &mut self,
        candidate: &impl FnSigProvider,
        criteria: &ApplicabilityCriteria,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> bool {
        (|| -> Result<()> {
            let mut constr = self.constrs.clone();
            let sig = candidate.fn_sig(self.sema).clone();

            if trace_enabled() {
                eprintln!(
                    "checking applicability of {}",
                    self.sema.format_signature(&sig)
                );
            }

            if ty_args.len() > sig.generics.len() || args.len() != sig.params.len() {
                if trace_enabled() {
                    eprintln!(
                        "  argument count mismatch: got {} type args, {} value args",
                        ty_args.len(),
                        args.len()
                    );
                }

                return Err(());
            }

            let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &Loc::Synthetic);

            for (&param, &arg) in iter::zip(&sig.generics, ty_args) {
                if trace_enabled() {
                    eprintln!("  checking type param `{}`", self.sema.format_ty(param));
                }

                constr
                    .add(
                        self.sema,
                        &mut DummyDiagCtx,
                        Constr {
                            kind: ConstrKind::Eq(arg, ty_param_map[param]),
                            provenance: candidate.applicability_constr_provenance(),
                        },
                    )
                    .inspect_err(|_| {
                        if trace_enabled() {
                            eprintln!("    unsat");
                        }
                    })?;
            }

            match (recv, sig.recv) {
                (Receiver::None, None) => {}

                (Receiver::Implicit(_), None) => {}

                (Receiver::Implicit(ty_id) | Receiver::Explicit(ty_id), Some(recv)) => {
                    let expected = self.make_recv_ty(recv, ReplaceTyArgs::Yes(&Loc::Synthetic));

                    if trace_enabled() {
                        eprintln!(
                            "  checking receiver: `{}` <: `{}`",
                            self.sema.format_ty(*ty_id),
                            self.sema.format_ty(expected),
                        );
                    }

                    constr
                        .add(
                            self.sema,
                            &mut DummyDiagCtx,
                            Constr {
                                kind: ConstrKind::Sub(*ty_id, expected),
                                provenance: candidate.applicability_constr_provenance(),
                            },
                        )
                        .inspect_err(|_| {
                            if trace_enabled() {
                                eprintln!("    unsat");
                            }
                        })?;
                }

                _ => return Err(()),
            }

            for (idx, (&param, &arg)) in iter::zip(&sig.params, args).enumerate() {
                if trace_enabled() {
                    eprintln!(
                        "  checking param #{}: `{}` -> `{}`",
                        idx + 1,
                        self.sema.format_ty(arg),
                        self.sema.format_ty(param)
                    );
                }

                let param = self.sema.tyck.subst(param, &ty_param_map);

                constr
                    .add(
                        self.sema,
                        &mut DummyDiagCtx,
                        Constr {
                            kind: ConstrKind::Coerce(arg, param),
                            provenance: candidate.applicability_constr_provenance(),
                        },
                    )
                    .inspect_err(|_| {
                        if trace_enabled() {
                            eprintln!("    unsat");
                        }
                    })?;
            }

            if !candidate.satisfies(self.sema, criteria) {
                if trace_enabled() {
                    eprintln!("  criteria unsatisfied");
                }

                return Err(());
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

        self.is_function_applicable(rhs, &ApplicabilityCriteria::default(), &recv, &args, &[])
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
            self.diag.emit(diag_provider.empty_candidate_set(self));

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
            self.diag.emit(diag_provider.ambiguity(self, &ambiguities));

            return Err(());
        }

        Ok(best)
    }
}
