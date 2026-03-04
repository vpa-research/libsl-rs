//! Overload resolution.

use std::cmp::Ordering;
use std::fmt::Write;
use std::iter;

use crate::diag::{Diag, DiagCtx, DummyDiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::DefId;
use crate::sema::resolve::ScopeKind;
use crate::sema::ty::TyId;
use crate::sema::tyck::Pass;
use crate::sema::tyck::constraints::{Constr, ConstrKind, ConstrProvenance};
use crate::sema::{Result, Sema};
use crate::{AccessId, WithLibSl, ast};

use super::FnTyInfo;

#[derive(Debug, Clone)]
pub struct OverloadResult {
    pub param_ty_ids: Vec<TyId>,
    pub ret_ty_id: TyId,
    pub def_id: DefId,
}

#[derive(Debug, Clone)]
pub enum Receiver {
    None,
}

pub trait FnInfoProvider {
    fn fn_info<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnTyInfo;

    fn applicability_constr_provenance(&self) -> ConstrProvenance;
}

impl<T: FnInfoProvider> FnInfoProvider for &'_ T {
    fn fn_info<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnTyInfo {
        (*self).fn_info(sema)
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        (*self).applicability_constr_provenance()
    }
}

struct DefFnInfoProvider(DefId);

impl FnInfoProvider for DefFnInfoProvider {
    fn fn_info<'a>(&'a self, sema: &'a Sema<'_>) -> &'a FnTyInfo {
        &sema.tyck.fns[self.0]
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        ConstrProvenance::Fn(self.0)
    }
}

pub trait OverloadDiagProvider<F: FnInfoProvider> {
    fn empty_candidate_set(&self, sema: &Sema<'_>) -> Diag;

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&F]) -> Diag;
}

struct CallOverloadDiagProvider<'a> {
    name: &'a str,
    loc: &'a Loc,
}

impl OverloadDiagProvider<DefFnInfoProvider> for CallOverloadDiagProvider<'_> {
    fn empty_candidate_set(&self, _sema: &Sema<'_>) -> Diag {
        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!("no function named `{}` found", self.name))
            .with_label(Label::primary(self.loc.clone()))
            .build()
    }

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&DefFnInfoProvider]) -> Diag {
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
    fn should_consider(&self, sema: &Sema<'_>, f: &impl FnInfoProvider) -> bool {
        if self.concrete_only && !f.fn_info(sema).generics.is_empty() {
            return false;
        }

        true
    }

    fn strengthen(&mut self, sema: &Sema<'_>, candidates: &[impl FnInfoProvider]) -> bool {
        if !self.concrete_only && self.strengthen_concrete(sema, candidates) {
            return true;
        }

        false
    }

    fn strengthen_concrete(&mut self, sema: &Sema<'_>, candidates: &[impl FnInfoProvider]) -> bool {
        let mut has_concrete = false;
        let mut has_parameterized = false;

        for candidate in candidates {
            if candidate.fn_info(sema).generics.is_empty() {
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
        callee_access_id: AccessId,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<(Receiver, DefId)> {
        let callee = &self.sema.libsl.accesses[callee_access_id];

        match &callee.kind {
            ast::AccessKind::Dummy => unreachable!(),
            ast::AccessKind::Name(a) => self.resolve_plain_name_callee(callee, a, args, ty_args),
            ast::AccessKind::Field(a) => self.resolve_method_callee(callee, a, args, ty_args),

            ast::AccessKind::Index(_) => {
                self.tyck_access(callee_access_id, None);
                self.diag.emit(
                    Diag::err()
                        .at(callee.loc.clone())
                        .with_msg("cannot call the result of an index expression")
                        .with_label(Label::primary(callee.loc.clone()))
                        .build(),
                );
                self.result = Err(());

                Err(())
            }

            ast::AccessKind::AutomatonField(a) => {
                self.resolve_automaton_method_callee(callee, a, args, ty_args)
            }
        }
    }

    fn resolve_plain_name_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessName,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<(Receiver, DefId)> {
        let name = a.name.to_string();
        let mut next_scope_id = Some(self.sema.name_res.access_scopes[access.id]);

        let mut candidates = vec![];
        let recv = Receiver::None;

        while let Some(scope_id) = next_scope_id {
            let scope = &self.sema.name_res.scopes[scope_id];
            next_scope_id = scope.parent;

            match &scope.kind {
                ScopeKind::Dummy => unreachable!(),

                ScopeKind::Params(_) | ScopeKind::Block { .. } => {
                    // regular scopes never define functions.
                }

                ScopeKind::Prelude | ScopeKind::Import(_) | ScopeKind::File(_) => {
                    if let Some(overloads) = scope.functions.get(&name) {
                        candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                            let provider = DefFnInfoProvider(def_id);

                            self.is_function_applicable(&provider, &recv, args, ty_args)
                                .then_some(provider)
                        }));
                    }
                }

                ScopeKind::SemanticTyEnum(_) => {
                    // enumerated semantic types do not define functions.
                }

                ScopeKind::Struct(_struct_def_id) => {
                    // TODO: inheritance?

                    if let Some(overloads) = scope.functions.get(&name) {
                        candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                            let provider = DefFnInfoProvider(def_id);

                            self.is_function_applicable(&provider, &recv, args, ty_args)
                                .then_some(provider)
                        }));
                    }
                }

                ScopeKind::Enum(_) => {
                    // enums never define functions.
                }

                ScopeKind::Automaton(_automaton_def_id) => {
                    // TODO: concepts?

                    if let Some(overloads) = scope.functions.get(&name) {
                        candidates.extend(overloads.clone().into_iter().filter_map(|def_id| {
                            let provider = DefFnInfoProvider(def_id);

                            self.is_function_applicable(&provider, &recv, args, ty_args)
                                .then_some(provider)
                        }));
                    }
                }
            }

            if !candidates.is_empty() {
                break;
            }
        }

        let diag_provider = CallOverloadDiagProvider {
            loc: &a.name.loc,
            name: &name,
        };

        self.select_overload(&candidates, &diag_provider)
            .map(|candidate| (recv, candidate.0))
    }

    fn resolve_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessField,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<(Receiver, DefId)> {
        todo!()
    }

    fn resolve_automaton_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessAutomatonField,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<(Receiver, DefId)> {
        unimplemented!()
    }

    pub fn is_function_applicable(
        &mut self,
        candidate: &impl FnInfoProvider,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> bool {
        (|| -> Result<()> {
            let mut constr = self.constrs.clone();
            let info = candidate.fn_info(self.sema).clone();

            if ty_args.len() > info.generics.len() || args.len() != info.params.len() {
                return Err(());
            }

            let ty_param_map = self.make_fresh_vars_for_ty_params(&info.generics);

            for (&param, &arg) in iter::zip(&info.generics, ty_args) {
                constr.add(
                    self.sema,
                    &mut DummyDiagCtx,
                    Constr {
                        kind: ConstrKind::Eq(arg, ty_param_map[param]),
                        provenance: candidate.applicability_constr_provenance(),
                    },
                )?;
            }

            match recv {
                Receiver::None => {
                    if info.recv.is_some() {
                        return Err(());
                    }
                }
            }

            for (&param, &arg) in iter::zip(&info.params, args) {
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

    fn is_lhs_more_specific(
        &mut self,
        lhs: &impl FnInfoProvider,
        rhs: &impl FnInfoProvider,
    ) -> bool {
        if lhs.fn_info(self.sema).params.len() != rhs.fn_info(self.sema).params.len() {
            return false;
        }

        let ty_param_map = lhs
            .fn_info(self.sema)
            .generics
            .clone()
            .into_iter()
            .map(|generic| (generic, self.sema.tyck.clone_param(generic)))
            .collect();

        let args = lhs
            .fn_info(self.sema)
            .params
            .clone()
            .into_iter()
            .map(|param| self.sema.tyck.subst(param, &ty_param_map))
            .collect::<Vec<_>>();

        let recv = match lhs.fn_info(self.sema).recv {
            Some(_) => unimplemented!(),
            None => Receiver::None,
        };

        self.is_function_applicable(rhs, &recv, &args, &[])
    }

    fn compare_overloads(
        &mut self,
        lhs: &impl FnInfoProvider,
        rhs: &impl FnInfoProvider,
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

    pub fn select_overload<'a, F: FnInfoProvider>(
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
