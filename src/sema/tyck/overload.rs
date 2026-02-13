//! Overload resolution.

use std::cmp::Ordering;
use std::fmt::{self, Display, Write};
use std::iter;

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{DefFunction, DefId};
use crate::sema::resolve::ScopeKind;
use crate::sema::ty::{TyArg, TyId};
use crate::sema::tyck::Pass;
use crate::sema::{Result, Sema};
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
        ty_args: &[TyArg],
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
        &self,
        candidates: &mut Vec<DefId>,
        overloads: &[DefId],
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyArg],
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
        ty_args: &[TyArg],
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
                            overloads,
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
                            overloads,
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
                            overloads,
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

        self.select_overload_candidate(
            &name,
            &a.name.loc,
            &candidates,
        )
    }

    fn resolve_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessField,
        args: &[TyId],
        ty_args: &[TyArg],
    ) -> Result<DefId> {
        todo!()
    }

    fn resolve_automaton_method_callee(
        &mut self,
        access: &'ast ast::Access,
        a: &'ast ast::AccessAutomatonField,
        args: &[TyId],
        ty_args: &[TyArg],
    ) -> Result<DefId> {
        unimplemented!()
    }

    fn is_function_applicable(
        &self,
        def_id: DefId,
        recv: &Receiver,
        args: &[TyId],
        ty_args: &[TyArg],
    ) -> bool {
        todo!()
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

                write!(
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
