use std::fmt::{Display, Write};

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::Sema;
use crate::sema::def::{DefEnum, DefKindTag};
use crate::sema::ty::{ConstructedTy, IntCtor, Ty, TyId};
use crate::sema::tyck::constraints::ConstrProvenance;
use crate::sema::tyck::overload::{ApplicabilityCriteria, FnSigProvider, OverloadDiagProvider};
use crate::sema::tyck::{BuiltinTys, FnSig, Pass};
use crate::util::format_list;
use crate::{ExprId, ast};

#[derive(Debug, Clone)]
pub enum NumericCmpOpOverload {
    SameSign(IntCtor),
    I64U64,
    U64I64,
}

impl From<IntCtor> for NumericCmpOpOverload {
    fn from(value: IntCtor) -> Self {
        Self::SameSign(value)
    }
}

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
    Lt(NumericCmpOpOverload),
    Le(NumericCmpOpOverload),
    Gt(NumericCmpOpOverload),
    Ge(NumericCmpOpOverload),
    EqNumeric(NumericCmpOpOverload),
    EqString,
    EqEnum,
    NeNumeric(NumericCmpOpOverload),
    NeString,
    NeEnum,
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

#[derive(Debug, Clone)]
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
    fn satisfies(&self, _sema: &mut Sema<'_>, criteria: &ApplicabilityCriteria) -> bool {
        let &ApplicabilityCriteria { proc_only } = criteria;

        if proc_only {
            return false;
        }

        true
    }

    fn fn_sig<'a>(&'a self, _sema: &'a Sema<'_>) -> &'a FnSig {
        &self.sig
    }

    fn applicability_constr_provenance(&self) -> ConstrProvenance {
        self.op.constr_provenance(&self.loc)
    }
}

pub type UnOpFnSigProvider = OpFnSigProvider<ast::UnOp>;
pub type BinOpFnSigProvider = OpFnSigProvider<ast::BinOp>;

pub struct OpOverloadDiagProvider<'a, O, F> {
    op: O,
    loc: &'a Loc,
    arg_tys: &'a [TyId],
    arg_loc: F,
}

impl<'a, O: Op, F> OpOverloadDiagProvider<'a, O, F>
where
    F: Fn(&Sema<'_>, usize) -> Loc,
{
    pub fn new(op: O, loc: &'a Loc, arg_tys: &'a [TyId], arg_loc: F) -> Self {
        Self {
            op,
            loc,
            arg_tys,
            arg_loc,
        }
    }

    fn label_operand_tys(&self, sema: &Sema<'_>, diag: &mut Diag) {
        for (idx, &arg_ty) in self.arg_tys.iter().enumerate() {
            diag.labels.push(
                Label::secondary((self.arg_loc)(sema, idx)).with_msg(format_args!(
                    "this operand has type `{}`",
                    sema.format_ty(arg_ty),
                )),
            );
        }
    }
}

impl<O: Op, F> OverloadDiagProvider<OpFnSigProvider<O>> for OpOverloadDiagProvider<'_, O, F>
where
    F: Fn(&Sema<'_>, usize) -> Loc,
{
    fn empty_candidate_set(&self, sema: &Sema<'_>) -> Diag {
        let mut diag = Diag::err()
            .at(self.loc.clone())
            .with_msg(format!(
                "no applicable overload of `{}` found for {}",
                self.op,
                format_list(self.arg_tys, |f, &ty_id| write!(
                    f,
                    "`{}`",
                    sema.format_ty(ty_id),
                ))
            ))
            .with_label(Label::primary(self.loc.clone()))
            .build();
        self.label_operand_tys(sema, &mut diag);

        diag
    }

    fn ambiguity(&self, sema: &Sema<'_>, ambiguities: &[&OpFnSigProvider<O>]) -> Diag {
        let mut possible_candidates = "the following candidates are possible:".to_owned();

        for &candidate in ambiguities {
            let _ = write!(
                possible_candidates,
                "\n- {}",
                format_list(&candidate.sig.params, |f, &ty_id| write!(
                    f,
                    "`{}`",
                    sema.format_ty(ty_id),
                )),
            );

            if !candidate.sig.generics.is_empty() {
                let _ = write!(
                    possible_candidates,
                    " for any {}",
                    format_list(&candidate.sig.generics, |f, &ty_id| write!(
                        f,
                        "`{}`",
                        sema.format_ty(ty_id),
                    )),
                );
            }
        }

        let mut diag = Diag::err()
            .at(self.loc.clone())
            .with_msg(format!(
                "type of `{}` is ambiguous: found {} possible candidates",
                self.op,
                ambiguities.len(),
            ))
            .with_label(Label::primary(self.loc.clone()))
            .with_note(possible_candidates)
            .build();
        self.label_operand_tys(sema, &mut diag);

        diag
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
    overload: impl Fn(NumericCmpOpOverload) -> OpOverload,
) -> Vec<OpFnSigProvider<O>> {
    builtin
        .int_tys()
        .into_iter()
        .map(|(ctor, ty)| {
            OpFnSigProvider::concrete(
                op.clone(),
                loc,
                overload(ctor.into()),
                vec![ty, ty],
                builtin.bool,
            )
        })
        .chain([
            OpFnSigProvider::concrete(
                op.clone(),
                loc,
                overload(NumericCmpOpOverload::I64U64),
                vec![builtin.int64, builtin.unsigned64],
                builtin.bool,
            ),
            OpFnSigProvider::concrete(
                op.clone(),
                loc,
                overload(NumericCmpOpOverload::U64I64),
                vec![builtin.unsigned64, builtin.int64],
                builtin.bool,
            ),
        ])
        .collect()
}

fn enum_op_overloads<O: Op + Clone>(
    sema: &mut Sema<'_>,
    op: O,
    loc: &Loc,
    overload: OpOverload,
    ret: TyId,
) -> Vec<OpFnSigProvider<O>> {
    #[allow(
        clippy::unnecessary_to_owned,
        reason = "it is actually necessary due to borrowck rules"
    )]
    sema.name_res.defs[DefKindTag::Enum]
        .to_vec()
        .into_iter()
        .map(|def_id| {
            let def = sema.name_res.def::<DefEnum>(def_id);
            let generics = def
                .generics
                .iter()
                .map(|&def_id| sema.tyck.def_tys[def_id])
                .collect::<Vec<_>>();
            let ty_id = sema.tyck.add_ctor_ty(def_id, generics.clone());
            let mut params = vec![];
            params.resize(O::ARITY, ty_id);

            OpFnSigProvider {
                op: op.clone(),
                loc: loc.clone(),
                sig: FnSig {
                    recv: None,
                    generics,
                    params,
                    ret: Some(ret),
                },
                overload: overload.clone(),
            }
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

                result.extend_from_slice(self.enum_eq_overloads.get_or_insert_with(|| {
                    enum_op_overloads(self.sema, op, loc, OpOverload::EqEnum, bool)
                }));

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

                result.extend_from_slice(self.enum_ne_overloads.get_or_insert_with(|| {
                    enum_op_overloads(self.sema, op, loc, OpOverload::NeEnum, bool)
                }));

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
