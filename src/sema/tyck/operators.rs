use std::fmt::{Display, Write};

use crate::ast;
use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::Sema;
use crate::sema::ty::{ConstructedTy, IntCtor, Ty, TyId};
use crate::sema::tyck::constraints::ConstrProvenance;
use crate::sema::tyck::overload::{FnSigProvider, OverloadDiagProvider};
use crate::sema::tyck::{BuiltinTys, FnSig, Pass};

#[derive(Debug, Clone)]
pub enum OpOverload {
    // unary operators.
    Plus(IntCtor),
    Neg(IntCtor),
    BitNot(IntCtor),
    Not,

    // binary operators.
    Mul(IntCtor),
    Div(IntCtor),
    Mod(IntCtor),
    AddNumeric(IntCtor),
    AddString,
    Sub(IntCtor),
    Sal(IntCtor),
    Sar(IntCtor),
    Shl(IntCtor),
    Shr(IntCtor),
    BitOr(IntCtor),
    BitXor(IntCtor),
    BitAnd(IntCtor),
    Lt(IntCtor),
    Le(IntCtor),
    Gt(IntCtor),
    Ge(IntCtor),
    EqNumeric(IntCtor),
    EqString,
    NeNumeric(IntCtor),
    NeString,
    InSet,
    InArray,
    NotInSet,
    NotInArray,
    Or,
    And,
}

pub trait Op: Display + Clone {
    const ARITY: usize;

    fn constr_provenance(&self, loc: &Loc) -> ConstrProvenance;
}

impl Op for ast::UnOp {
    const ARITY: usize = 1;

    fn constr_provenance(&self, loc: &Loc) -> ConstrProvenance {
        ConstrProvenance::UnOp(*self, loc.clone())
    }
}

impl Op for ast::BinOp {
    const ARITY: usize = 2;

    fn constr_provenance(&self, loc: &Loc) -> ConstrProvenance {
        ConstrProvenance::BinOp(*self, loc.clone())
    }
}

pub struct OpFnSigProvider<O> {
    op: O,
    loc: Loc,
    sig: FnSig,
    pub overload: OpOverload,
}

impl<O: Op> OpFnSigProvider<O> {
    fn concrete(op: O, loc: &Loc, overload: OpOverload, params: Vec<TyId>, result: TyId) -> Self {
        Self {
            op,
            loc: loc.clone(),
            sig: FnSig {
                recv: None,
                generics: vec![],
                params,
                ret: Some(result),
            },
            overload,
        }
    }

    fn generic<const N: usize>(
        sema: &mut Sema<'_>,
        op: O,
        loc: &Loc,
        overload: OpOverload,
        ty_params: [&'static str; N],
        sig: impl FnOnce(&mut Sema<'_>, [TyId; N]) -> (Vec<TyId>, TyId),
    ) -> Self {
        let generics = ty_params.map(|name| sema.tyck.fresh_param(name.into()));
        let (params, ret) = sig(sema, generics);

        Self {
            op,
            loc: loc.clone(),
            sig: FnSig {
                recv: None,
                generics: generics.to_vec(),
                params,
                ret: Some(ret),
            },
            overload,
        }
    }

    pub fn fn_sig(&self) -> &FnSig {
        &self.sig
    }
}

impl<O: Op> FnSigProvider for OpFnSigProvider<O> {
    fn fn_sig<'a>(&'a self, _sema: &'a Sema<'_>) -> &'a FnSig {
        &self.sig
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        self.op.constr_provenance(&self.loc)
    }
}

pub type UnOpFnSigProvider = OpFnSigProvider<ast::UnOp>;
pub type BinOpFnSigProvider = OpFnSigProvider<ast::BinOp>;

pub struct OpOverloadDiagProvider<'a, O> {
    op: O,
    loc: &'a Loc,
}

impl<'a, O: Op> OpOverloadDiagProvider<'a, O> {
    pub fn new(op: O, loc: &'a Loc) -> Self {
        Self { op, loc }
    }
}

impl<O: Op> OverloadDiagProvider<OpFnSigProvider<O>> for OpOverloadDiagProvider<'_, O> {
    fn empty_candidate_set(&self, _sema: &Sema<'_>) -> Diag {
        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!("no applicable overload for `{}` found", self.op))
            .with_label(Label::primary(self.loc.clone()))
            .build()
    }

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&OpFnSigProvider<O>]) -> Diag {
        let mut possible_candidates = "the following candidates are possible:".to_owned();

        for &candidate in ambiguities {
            let _ = write!(possible_candidates, "\n  - ");

            for (idx, &ty_id) in candidate.sig.params.iter().enumerate() {
                if idx > 0 && !(idx == 1 && O::ARITY == 2) {
                    let _ = write!(possible_candidates, ", ");
                }

                if idx + 1 == O::ARITY {
                    let _ = write!(possible_candidates, "and ");
                }

                let _ = write!(possible_candidates, "{}", sema.format_ty(ty_id));
            }
        }

        Diag::err()
            .at(self.loc.clone())
            .with_msg(format!(
                "type of `{}` is ambiguous: found {} possible candidates",
                self.op,
                ambiguities.len(),
            ))
            .with_label(Label::primary(self.loc.clone()))
            .with_note(possible_candidates)
            .build()
    }
}

fn arith<O: Op + Clone>(
    op: O,
    loc: &Loc,
    builtin: &BuiltinTys,
    overload: impl Fn(IntCtor) -> OpOverload,
) -> Vec<OpFnSigProvider<O>> {
    builtin
        .int_tys()
        .into_iter()
        .map(|(ctor, ty)| {
            OpFnSigProvider::concrete(op.clone(), loc, overload(ctor), vec![ty, ty], ty)
        })
        .collect()
}

fn cmp<O: Op + Clone>(
    op: O,
    loc: &Loc,
    builtin: &BuiltinTys,
    overload: impl Fn(IntCtor) -> OpOverload,
) -> Vec<OpFnSigProvider<O>> {
    builtin
        .int_tys()
        .into_iter()
        .map(|(ctor, ty)| {
            OpFnSigProvider::concrete(op.clone(), loc, overload(ctor), vec![ty, ty], builtin.bool)
        })
        .collect()
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    pub(super) fn overloads_for_unary(
        &mut self,
        op: ast::UnOp,
        loc: &Loc,
    ) -> Vec<UnOpFnSigProvider> {
        type P = UnOpFnSigProvider;

        let b = &self.sema.tyck.builtin;

        match op {
            ast::UnOp::Plus => arith(op, loc, b, OpOverload::Plus),
            ast::UnOp::Neg => arith(op, loc, b, OpOverload::Neg),
            ast::UnOp::BitNot => arith(op, loc, b, OpOverload::BitNot),
            ast::UnOp::Not => vec![P::concrete(op, loc, OpOverload::Not, vec![b.bool], b.bool)],
        }
    }

    pub(super) fn overloads_for_binary(
        &mut self,
        op: ast::BinOp,
        loc: &Loc,
    ) -> Vec<BinOpFnSigProvider> {
        type P = BinOpFnSigProvider;

        let b @ &BuiltinTys { bool, string, .. } = &self.sema.tyck.builtin;

        match op {
            ast::BinOp::Mul => arith(op, loc, b, OpOverload::Mul),
            ast::BinOp::Div => arith(op, loc, b, OpOverload::Div),
            ast::BinOp::Mod => arith(op, loc, b, OpOverload::Mod),

            ast::BinOp::Add => {
                let mut result = arith(op, loc, b, OpOverload::AddNumeric);
                result.extend([P::concrete(
                    op,
                    loc,
                    OpOverload::AddString,
                    vec![string, string],
                    string,
                )]);

                result
            }

            ast::BinOp::Sub => arith(op, loc, b, OpOverload::Sub),
            ast::BinOp::Sal => arith(op, loc, b, OpOverload::Sal),
            ast::BinOp::Sar => arith(op, loc, b, OpOverload::Sar),
            ast::BinOp::Shl => arith(op, loc, b, OpOverload::Shl),
            ast::BinOp::Shr => arith(op, loc, b, OpOverload::Shr),
            ast::BinOp::BitOr => arith(op, loc, b, OpOverload::BitOr),
            ast::BinOp::BitXor => arith(op, loc, b, OpOverload::BitXor),
            ast::BinOp::BitAnd => arith(op, loc, b, OpOverload::BitAnd),
            ast::BinOp::Lt => cmp(op, loc, b, OpOverload::Lt),
            ast::BinOp::Le => cmp(op, loc, b, OpOverload::Le),
            ast::BinOp::Gt => cmp(op, loc, b, OpOverload::Gt),
            ast::BinOp::Ge => cmp(op, loc, b, OpOverload::Ge),

            ast::BinOp::Eq => {
                let mut result = cmp(op, loc, b, OpOverload::EqNumeric);
                result.extend([P::concrete(
                    op,
                    loc,
                    OpOverload::EqString,
                    vec![string, string],
                    bool,
                )]);

                result
            }

            ast::BinOp::Ne => {
                let mut result = cmp(op, loc, b, OpOverload::NeNumeric);
                result.extend([P::concrete(
                    op,
                    loc,
                    OpOverload::NeString,
                    vec![string, string],
                    bool,
                )]);

                result
            }

            ast::BinOp::In => vec![
                P::generic(self.sema, op, loc, OpOverload::InSet, ["T"], |sema, [t]| {
                    let set = sema.tyck.add_ty(Ty::Ctor(ConstructedTy {
                        ctor: sema.name_res.prelude_defs.set,
                        args: vec![t],
                    }));

                    (vec![t, set], bool)
                }),
                P::generic(
                    self.sema,
                    op,
                    loc,
                    OpOverload::InArray,
                    ["T"],
                    |sema, [t]| {
                        let array = sema.tyck.add_ty(Ty::Ctor(ConstructedTy {
                            ctor: sema.name_res.prelude_defs.array,
                            args: vec![t],
                        }));

                        (vec![t, array], bool)
                    },
                ),
            ],

            ast::BinOp::NotIn => vec![
                P::generic(
                    self.sema,
                    op,
                    loc,
                    OpOverload::NotInSet,
                    ["T"],
                    |sema, [t]| {
                        let set = sema.tyck.add_ty(Ty::Ctor(ConstructedTy {
                            ctor: sema.name_res.prelude_defs.set,
                            args: vec![t],
                        }));

                        (vec![t, set], bool)
                    },
                ),
                P::generic(
                    self.sema,
                    op,
                    loc,
                    OpOverload::NotInArray,
                    ["T"],
                    |sema, [t]| {
                        let array = sema.tyck.add_ty(Ty::Ctor(ConstructedTy {
                            ctor: sema.name_res.prelude_defs.array,
                            args: vec![t],
                        }));

                        (vec![t, array], bool)
                    },
                ),
            ],

            ast::BinOp::Or => vec![P::concrete(op, loc, OpOverload::Or, vec![bool, bool], bool)],
            ast::BinOp::And => vec![P::concrete(op, loc, OpOverload::Or, vec![bool, bool], bool)],
        }
    }
}
