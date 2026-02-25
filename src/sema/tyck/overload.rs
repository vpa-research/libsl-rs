//! Overload resolution.

use std::cmp::Ordering;
use std::fmt::Write;
use std::iter;

use slotmap::SparseSecondaryMap;

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::Result;
use crate::sema::def::{DefFunction, DefId};
use crate::sema::resolve::ScopeKind;
use crate::sema::ty::TyId;
use crate::sema::tyck::Pass;
use crate::sema::tyck::constraints::{Constr, ConstrKind, ConstrProvenance, VarProvenance};
use crate::{AccessId, WithLibSl, ast};

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

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    pub(super) fn resolve_callee(
        &mut self,
        callee_access_id: AccessId,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
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

                Err(())
            }

            ast::AccessKind::AutomatonField(a) => {
                self.resolve_automaton_method_callee(callee, a, args, ty_args)
            }
        }
    }

    fn find_applicable_overloads(
        &mut self,
        candidates: &mut Vec<DefId>,
        overloads: &[DefId],
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) {
        candidates.extend(
            overloads
                .iter()
                .filter(|&&def_id| self.is_function_applicable(def_id, recv, args, ty_args)),
        );
    }

    fn resolve_plain_name_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessName,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        let name = a.name.to_string();
        let mut next_scope_id = Some(self.sema.name_res.access_scopes[access.id]);

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
                    if let Some(overloads) = scope.functions.get(&name) {
                        self.find_applicable_overloads(
                            &mut candidates,
                            &overloads.clone(),
                            &Receiver::None,
                            args,
                            ty_args,
                        );
                    }
                }

                ScopeKind::SemanticTyEnum(_) => {
                    // enumerated semantic types do not define functions.
                }

                ScopeKind::Struct(_struct_def_id) => {
                    // TODO: inheritance?

                    if let Some(overloads) = scope.functions.get(&name) {
                        self.find_applicable_overloads(
                            &mut candidates,
                            &overloads.clone(),
                            &Receiver::None,
                            args,
                            ty_args,
                        );
                    }
                }

                ScopeKind::Enum(_) => {
                    // enums never define functions.
                }

                ScopeKind::Automaton(_automaton_def_id) => {
                    // TODO: concepts?

                    if let Some(overloads) = scope.functions.get(&name) {
                        self.find_applicable_overloads(
                            &mut candidates,
                            &overloads.clone(),
                            &Receiver::None,
                            args,
                            ty_args,
                        );
                    }
                }
            }

            if !candidates.is_empty() {
                break;
            }
        }

        self.select_overload_candidate(&name, &a.name.loc, &candidates)
    }

    fn resolve_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessField,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        todo!()
    }

    fn resolve_automaton_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessAutomatonField,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> Result<DefId> {
        unimplemented!()
    }

    fn is_function_applicable(
        &mut self,
        def_id: DefId,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyId],
    ) -> bool {
        (|| -> Result<()> {
            let mut constr = self.constrs.clone();
            let info = self.sema.tyck.fns[def_id].clone();

            if ty_args.len() > info.generics.len() || args.len() != info.params.len() {
                return Err(());
            }

            let ty_param_map = info
                .generics
                .iter()
                .map(|&generic| (generic, self.fresh_var(VarProvenance::Generic(generic))))
                .collect::<SparseSecondaryMap<_, _>>();

            for (&param, &arg) in iter::zip(&info.generics, ty_args) {
                constr.add(
                    self.sema,
                    self.diag,
                    Constr {
                        kind: ConstrKind::Eq(ty_param_map[param], arg),
                        provenance: ConstrProvenance::Fn(def_id),
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
                    self.diag,
                    Constr {
                        kind: ConstrKind::Coerce(arg, param),
                        provenance: ConstrProvenance::Fn(def_id),
                    },
                )?;
            }

            Ok(())
        })()
        .is_ok()
    }

    fn is_lhs_more_specific(&self, lhs: DefId, rhs: DefId) -> bool {
        todo!()
    }

    fn compare_overloads(&self, lhs: DefId, rhs: DefId) -> Option<Ordering> {
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

    fn select_overload_candidate(
        &mut self,
        name: &str,
        loc: &Loc,
        candidates: &[DefId],
    ) -> Result<DefId> {
        if candidates.is_empty() {
            self.diag.emit(
                Diag::err()
                    .at(loc.clone())
                    .with_msg(format!("no function named `{name}` found"))
                    .with_label(Label::primary(loc.clone()))
                    .build(),
            );

            return Err(());
        }

        let mut best = candidates[0];
        let mut ambiguities = vec![];

        for &candidate in candidates.iter().skip(1) {
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

        if !ambiguities.is_empty() {
            let mut candidates_considered = "the following candidates are possible:".to_owned();

            for candidate in iter::once(best).chain(ambiguities.iter().copied()) {
                let def = &self.sema.name_res.defs[candidate];

                let _ = write!(
                    candidates_considered,
                    "\n  - {} defined at {}",
                    self.sema.format_signature(candidate),
                    def.loc.with_libsl(self.sema.libsl),
                );
            }

            self.diag.emit(
                Diag::err()
                    .at(loc.clone())
                    .with_msg(format!(
                        "the call for `{name}` is ambiguous: found {} applicable overloads",
                        ambiguities.len() + 1
                    ))
                    .with_label(
                        Label::primary(loc.clone())
                            .with_msg("cannot determine which function this refers to"),
                    )
                    .build(),
            );

            return Err(());
        }

        Ok(best)
    }
}
