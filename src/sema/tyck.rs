//! Type checking and inference for LibSL.

use std::collections::HashMap;
use std::fmt::{self, Display, Write};
use std::iter;

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap};

use crate::ast::Variance;
use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{
    DefAction, DefAnnotation, DefAutomaton, DefFunction, DefId, DefKind, FunctionKind,
};
use crate::sema::ty::{BuiltinTyCtor, ConstructedTy, FloatCtor, IntCtor, IntWidth, Ty, TyId};
use crate::sema::tyck::constraints::{ConstrProvenance, ConstrSet, VarProvenance};
use crate::sema::tyck::operators::{Op, OpFnSigProvider, OpOverload, OpOverloadDiagProvider};
use crate::sema::tyck::overload::Receiver;
use crate::sema::{Result, Sema};
use crate::{AccessId, DeclId, ExprId, PredId, StmtId, TyExprId, ast};

use self::constraints::SubtypeBoundKind;

use super::def::{DefEnum, DefKindProject, DefStruct};
use super::resolve::NameRes;

mod constraints;
mod operators;
mod overload;

#[derive(Debug, Default)]
pub struct BuiltinTys {
    pub error: TyId,
    pub null: TyId,
    pub int8: TyId,
    pub int16: TyId,
    pub int32: TyId,
    pub int64: TyId,
    pub unsigned8: TyId,
    pub unsigned16: TyId,
    pub unsigned32: TyId,
    pub unsigned64: TyId,
    pub float32: TyId,
    pub float64: TyId,
    pub bool: TyId,
    pub char: TyId,
    pub string: TyId,
    pub void: TyId,
    pub any: TyId,
    pub nothing: TyId,
}

impl BuiltinTys {
    pub fn int_tys(&self) -> [(IntCtor, TyId); 8] {
        [
            (IntCtor::I8, self.int8),
            (IntCtor::I16, self.int16),
            (IntCtor::I32, self.int32),
            (IntCtor::I64, self.int64),
            (IntCtor::U8, self.unsigned8),
            (IntCtor::U16, self.unsigned16),
            (IntCtor::U32, self.unsigned32),
            (IntCtor::U64, self.unsigned64),
        ]
    }
}

#[derive(Debug, Clone)]
pub struct FnSig {
    pub recv: Option<DefId>,
    pub generics: Vec<TyId>,
    pub params: Vec<TyId>,
    pub ret: Option<TyId>,
}

#[derive(Debug, Clone)]
pub struct TyParam {
    pub def_id: Option<DefId>,
    pub name: String,
}

#[derive(Debug, Default)]
pub struct TyCk {
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: HashMap<Ty, TyId>,
    pub builtin: BuiltinTys,
    pub exprs: SecondaryMap<ExprId, TyId>,
    pub accesses: SecondaryMap<AccessId, TyId>,
    pub ty_exprs: SecondaryMap<TyExprId, TyId>,

    // maps variables and generics to their types.
    pub def_tys: SecondaryMap<DefId, TyId>,

    pub sigs: SparseSecondaryMap<DefId, FnSig>,
    pub param_variances: SparseSecondaryMap<DefId, Vec<Variance>>,
    pub ty_params: Vec<TyParam>,
    pub operators: SparseSecondaryMap<ExprId, OpOverload>,

    // applicable to enums and automata.
    pub underlying_tys: SparseSecondaryMap<DefId, TyId>,

    // for each type stores a vec of inference variable occurring in it.
    var_occurrences: SecondaryMap<TyId, Vec<TyId>>,

    // for each variable stores where it came from.
    var_provenances: Vec<VarProvenance>,

    // for each type stores other types that refer to it.
    ty_preds: SecondaryMap<TyId, Vec<TyId>>,

    // an append-only sequence of all registered types.
    ty_vec: Vec<TyId>,
}

fn occurring_vars(var_occurrences: &SecondaryMap<TyId, Vec<TyId>>, ty: &Ty) -> Vec<TyId> {
    let mut occurrences = vec![];

    match ty {
        Ty::Error => {}

        Ty::Param(_) => {}

        Ty::Ctor(t) => {
            for &arg in &t.args {
                occurrences.extend(&var_occurrences[arg])
            }
        }

        Ty::Var(_) => {}

        Ty::Null => {}
    }

    occurrences
}

fn add_preds(preds: &mut SecondaryMap<TyId, Vec<TyId>>, ty: &Ty, ty_id: TyId) {
    match ty {
        Ty::Error => {}

        Ty::Param(_) => {}

        Ty::Ctor(t) => {
            for &arg in &t.args {
                let p = preds.entry(arg).unwrap().or_default();

                if !p.contains(&ty_id) {
                    p.push(ty_id);
                }
            }
        }

        Ty::Var(_) => {}

        Ty::Null => {}
    }
}

impl TyCk {
    pub fn add_ty(&mut self, ty: Ty) -> TyId {
        *self.ty_dedup.entry(ty).or_insert_with_key(|ty| {
            let ty_id = self.tys.insert(ty.clone());
            self.var_occurrences
                .insert(ty_id, occurring_vars(&self.var_occurrences, ty));
            self.ty_vec.push(ty_id);
            add_preds(&mut self.ty_preds, ty, ty_id);

            ty_id
        })
    }

    pub fn add_ctor_ty(&mut self, ctor: DefId, args: Vec<TyId>) -> TyId {
        self.add_ty(Ty::Ctor(ConstructedTy { ctor, args }))
    }

    pub fn subst(&mut self, ty_id: TyId, map: &SparseSecondaryMap<TyId, TyId>) -> TyId {
        if let Some(&replacement) = map.get(ty_id) {
            return replacement;
        }

        let ty = match &self.tys[ty_id] {
            Ty::Error => return ty_id,

            Ty::Param(_) => return ty_id,

            Ty::Ctor(t) => {
                let mut t = t.clone();

                for arg in &mut t.args {
                    *arg = self.subst(*arg, map);
                }

                Ty::Ctor(t)
            }

            Ty::Var(_) => return ty_id,
            Ty::Null => return ty_id,
        };

        self.add_ty(ty)
    }

    fn make_param_for(&mut self, name_res: &NameRes, def_id: DefId) -> TyId {
        let idx = self.ty_params.len();
        self.ty_params.push(TyParam {
            def_id: Some(def_id),
            name: name_res.defs[def_id].name.clone(),
        });

        self.add_ty(Ty::Param(idx))
    }

    pub fn fresh_param(&mut self, name: String) -> TyId {
        let idx = self.ty_params.len();
        self.ty_params.push(TyParam { def_id: None, name });

        self.add_ty(Ty::Param(idx))
    }

    pub fn clone_param(&mut self, ty_id: TyId) -> TyId {
        let idx = self.tys[ty_id].as_param().unwrap();
        let new_idx = self.ty_params.len();
        self.ty_params.push(self.ty_params[idx].clone());

        self.add_ty(Ty::Param(new_idx))
    }

    pub fn is_subty(&self, lhs_ty_id: TyId, rhs_ty_id: TyId, constrs: Option<&ConstrSet>) -> bool {
        let lhs_ty_id = constrs.map(|set| set.repr(lhs_ty_id)).unwrap_or(lhs_ty_id);
        let rhs_ty_id = constrs.map(|set| set.repr(rhs_ty_id)).unwrap_or(rhs_ty_id);

        if lhs_ty_id == rhs_ty_id {
            return true;
        }

        if rhs_ty_id == self.builtin.any {
            return true;
        }

        match (&self.tys[lhs_ty_id], &self.tys[rhs_ty_id]) {
            (Ty::Error, _) | (_, Ty::Error) => true,

            (Ty::Var(l), _) => {
                if let Some(constrs) = constrs {
                    constrs.has_var_bound(self, *l, SubtypeBoundKind::Upper, rhs_ty_id)
                } else {
                    false
                }
            }

            (_, Ty::Var(r)) => {
                if let Some(constrs) = constrs {
                    constrs.has_var_bound(self, *r, SubtypeBoundKind::Lower, rhs_ty_id)
                } else {
                    false
                }
            }

            (Ty::Ctor(l), Ty::Ctor(r)) if l.ctor == r.ctor => {
                let variances = &self.param_variances[l.ctor];

                variances
                    .iter()
                    .zip(iter::zip(&l.args, &r.args))
                    .all(|(variance, (&l, &r))| match variance {
                        Variance::Covariant => self.is_subty(l, r, constrs),
                        Variance::Contravariant => self.is_subty(r, l, constrs),

                        Variance::Invariant => {
                            let l = constrs.map(|set| set.repr(l)).unwrap_or(l);
                            let r = constrs.map(|set| set.repr(r)).unwrap_or(r);

                            l == r
                        }
                    })
            }

            (Ty::Ctor(_) | Ty::Param(_) | Ty::Null, _) => false,
        }
    }

    pub fn lub(&mut self, lhs_ty_id: TyId, rhs_ty_id: TyId, constrs: Option<&ConstrSet>) -> TyId {
        let lhs_ty_id = constrs.map(|set| set.repr(lhs_ty_id)).unwrap_or(lhs_ty_id);
        let rhs_ty_id = constrs.map(|set| set.repr(rhs_ty_id)).unwrap_or(rhs_ty_id);

        if lhs_ty_id == rhs_ty_id {
            return lhs_ty_id;
        }

        if lhs_ty_id == self.builtin.error || rhs_ty_id == self.builtin.error {
            return self.builtin.error;
        }

        if self.is_subty(lhs_ty_id, rhs_ty_id, constrs) {
            return lhs_ty_id;
        }

        if self.is_subty(rhs_ty_id, lhs_ty_id, constrs) {
            return rhs_ty_id;
        }

        match (&self.tys[lhs_ty_id], &self.tys[rhs_ty_id]) {
            (Ty::Ctor(l), Ty::Ctor(r)) if l.ctor == r.ctor => {
                let ctor = l.ctor;
                let variances = self.param_variances[ctor].clone();

                let Some(args) = variances
                    .into_iter()
                    .zip(iter::zip(l.args.clone(), r.args.clone()))
                    .map(|(variance, (l, r))| match variance {
                        Variance::Covariant => Some(self.lub(l, r, constrs)),
                        Variance::Contravariant => self.glb(l, r, constrs),

                        Variance::Invariant => {
                            let l = constrs.map(|set| set.repr(l)).unwrap_or(l);
                            let r = constrs.map(|set| set.repr(r)).unwrap_or(r);

                            (l == r).then_some(l)
                        }
                    })
                    .collect::<Option<Vec<_>>>()
                else {
                    return self.builtin.any;
                };

                self.add_ctor_ty(ctor, args)
            }

            (Ty::Error | Ty::Ctor(_) | Ty::Param(_) | Ty::Var(_) | Ty::Null, _) => self.builtin.any,
        }
    }

    pub fn glb(
        &mut self,
        lhs_ty_id: TyId,
        rhs_ty_id: TyId,
        constrs: Option<&ConstrSet>,
    ) -> Option<TyId> {
        let lhs_ty_id = constrs.map(|set| set.repr(lhs_ty_id)).unwrap_or(lhs_ty_id);
        let rhs_ty_id = constrs.map(|set| set.repr(rhs_ty_id)).unwrap_or(rhs_ty_id);

        if lhs_ty_id == rhs_ty_id {
            return Some(lhs_ty_id);
        }

        if lhs_ty_id == self.builtin.error || rhs_ty_id == self.builtin.error {
            return Some(self.builtin.error);
        }

        if self.is_subty(lhs_ty_id, rhs_ty_id, constrs) {
            return Some(rhs_ty_id);
        }

        if self.is_subty(rhs_ty_id, lhs_ty_id, constrs) {
            return Some(lhs_ty_id);
        }

        match (&self.tys[lhs_ty_id], &self.tys[rhs_ty_id]) {
            (Ty::Ctor(l), Ty::Ctor(r)) if l.ctor == r.ctor => {
                let ctor = l.ctor;
                let variances = self.param_variances[ctor].clone();

                let args = variances
                    .into_iter()
                    .zip(iter::zip(l.args.clone(), r.args.clone()))
                    .map(|(variance, (l, r))| match variance {
                        Variance::Covariant => self.glb(l, r, constrs),
                        Variance::Contravariant => Some(self.lub(l, r, constrs)),

                        Variance::Invariant => {
                            let l = constrs.map(|set| set.repr(l)).unwrap_or(l);
                            let r = constrs.map(|set| set.repr(r)).unwrap_or(r);

                            (l == r).then_some(l)
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;

                Some(self.add_ctor_ty(ctor, args))
            }

            (Ty::Error | Ty::Ctor(_) | Ty::Param(_) | Ty::Var(_) | Ty::Null, _) => None,
        }
    }
}

impl Sema<'_> {
    /// Performs type checking and inference.
    pub fn tyck(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }

    /// Formats a type.
    pub fn format_ty(&self, ty_id: TyId) -> impl Display {
        let ty = &self.tyck.tys[ty_id];

        fmt::from_fn(move |f| {
            match ty {
                Ty::Error => write!(f, "[error]"),

                &Ty::Param(n) => write!(f, "{}", self.tyck.ty_params[n].name),

                Ty::Ctor(t) if t.ctor == self.name_res.prelude_defs.pointer => {
                    write!(f, "*({})", self.format_ty(t.args[0]))
                }

                Ty::Ctor(t) => {
                    write!(f, "{}", self.name_res.defs[t.ctor].name)?;

                    if !t.args.is_empty() {
                        write!(f, "<")?;

                        for (idx, &arg) in t.args.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}", self.format_ty(arg))?;
                        }

                        write!(f, ">")?;
                    }

                    Ok(())
                }

                // TODO: store a readable name for inference variables.
                Ty::Var(n) => write!(f, "?T{n}"),

                Ty::Null => write!(f, "null"),
            }
        })
    }

    /// Formats the function signature of a [`DefFunction`].
    pub fn format_def_signature(&self, def_id: DefId) -> impl Display {
        let sig = &self.tyck.sigs[def_id];

        fmt::from_fn(move |f| {
            // TODO: receiver.

            write!(
                f,
                "{}{}",
                self.name_res.defs[def_id].name,
                self.format_signature(sig)
            )
        })
    }

    /// Formats a function signature (without the receiver).
    pub fn format_signature(&self, sig: &FnSig) -> impl Display {
        fmt::from_fn(move |f| {
            if !sig.generics.is_empty() {
                write!(f, "<")?;

                for (idx, &generic) in sig.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    let param = self.tyck.tys[generic].as_param().unwrap();

                    write!(f, "{}", self.tyck.ty_params[param].name)?;
                }

                write!(f, ">")?;
            }

            write!(f, "(")?;

            for (idx, &param_ty_id) in sig.params.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.format_ty(param_ty_id))?;
            }

            write!(f, ")")?;

            if let Some(ret) = sig.ret {
                write!(f, ": {}", self.format_ty(ret))?;
            }

            Ok(())
        })
    }
}

struct Pass<'ast, 's, D> {
    sema: &'s mut Sema<'ast>,
    diag: &'s mut D,
    result: Result,
    constrs: ConstrSet,
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn new(sema: &'s mut Sema<'ast>, diag: &'s mut D) -> Self {
        Self {
            sema,
            diag,
            result: Ok(()),
            constrs: Default::default(),
        }
    }

    fn run(mut self) -> Result {
        self.init_builtin_tys();
        self.early_tyck_decls();
        self.tyck_decls();
        self.tyck_decl_bodies();

        self.result
    }

    fn init_builtin_tys(&mut self) {
        let defs = &self.sema.name_res.prelude_defs;

        let builtins: &[(fn(&mut BuiltinTys) -> &mut TyId, DefId, BuiltinTyCtor)] = &[
            (
                |t| &mut t.int8,
                defs.int8,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I8,
                    signed: true,
                }),
            ),
            (
                |t| &mut t.int16,
                defs.int16,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I16,
                    signed: true,
                }),
            ),
            (
                |t| &mut t.int32,
                defs.int32,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I32,
                    signed: true,
                }),
            ),
            (
                |t| &mut t.int64,
                defs.int64,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I64,
                    signed: true,
                }),
            ),
            (
                |t| &mut t.unsigned8,
                defs.unsigned8,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I8,
                    signed: false,
                }),
            ),
            (
                |t| &mut t.unsigned16,
                defs.unsigned16,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I16,
                    signed: false,
                }),
            ),
            (
                |t| &mut t.unsigned32,
                defs.unsigned32,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I32,
                    signed: false,
                }),
            ),
            (
                |t| &mut t.unsigned64,
                defs.unsigned64,
                BuiltinTyCtor::Int(IntCtor {
                    width: IntWidth::I64,
                    signed: false,
                }),
            ),
            (
                |t| &mut t.float32,
                defs.float32,
                BuiltinTyCtor::Float(FloatCtor::F32),
            ),
            (
                |t| &mut t.float64,
                defs.float64,
                BuiltinTyCtor::Float(FloatCtor::F64),
            ),
            (|t| &mut t.bool, defs.bool, BuiltinTyCtor::Bool),
            (|t| &mut t.char, defs.char, BuiltinTyCtor::Char),
            (|t| &mut t.string, defs.string, BuiltinTyCtor::String),
            (|t| &mut t.void, defs.void, BuiltinTyCtor::Void),
            (|t| &mut t.any, defs.any, BuiltinTyCtor::Any),
            (|t| &mut t.nothing, defs.nothing, BuiltinTyCtor::Nothing),
        ];

        for &(prelude, def_id, ref ctor) in builtins {
            self.sema.name_res.defs[def_id].kind = ctor.clone().into();
            let ty_id = self.sema.tyck.add_ty(Ty::Ctor(ConstructedTy {
                ctor: def_id,
                args: vec![],
            }));
            self.sema
                .tyck
                .param_variances
                .insert(def_id, ctor.variance().into());

            *prelude(&mut self.sema.tyck.builtin) = ty_id;
        }

        self.sema.tyck.builtin.error = self.sema.tyck.add_ty(Ty::Error);
        self.sema.tyck.builtin.null = self.sema.tyck.add_ty(Ty::Null);

        let ctors = &[
            (self.sema.name_res.prelude_defs.array, BuiltinTyCtor::Array),
            (self.sema.name_res.prelude_defs.set, BuiltinTyCtor::Set),
            (
                self.sema.name_res.prelude_defs.pointer,
                BuiltinTyCtor::Pointer,
            ),
        ];

        for (def_id, ctor) in ctors {
            self.sema.name_res.defs[*def_id].kind = ctor.clone().into();
            self.sema
                .tyck
                .param_variances
                .insert(*def_id, ctor.variance().into());
        }
    }

    fn int_ctor_ty(&self, ctor: &IntCtor) -> TyId {
        let builtin = &self.sema.tyck.builtin;

        match ctor {
            IntCtor {
                width: IntWidth::I8,
                signed: false,
            } => builtin.int8,

            IntCtor {
                width: IntWidth::I16,
                signed: false,
            } => builtin.int16,

            IntCtor {
                width: IntWidth::I32,
                signed: false,
            } => builtin.int32,

            IntCtor {
                width: IntWidth::I64,
                signed: false,
            } => builtin.int64,

            IntCtor {
                width: IntWidth::I8,
                signed: true,
            } => builtin.unsigned8,

            IntCtor {
                width: IntWidth::I16,
                signed: true,
            } => builtin.unsigned16,

            IntCtor {
                width: IntWidth::I32,
                signed: true,
            } => builtin.unsigned32,

            IntCtor {
                width: IntWidth::I64,
                signed: true,
            } => builtin.unsigned64,
        }
    }

    fn int_lit_ty(&self, lit: &ast::IntLit) -> TyId {
        let builtin = &self.sema.tyck.builtin;

        match lit {
            ast::IntLit::I8(_) => builtin.int8,
            ast::IntLit::U8(_) => builtin.unsigned8,
            ast::IntLit::I16(_) => builtin.int16,
            ast::IntLit::U16(_) => builtin.unsigned16,
            ast::IntLit::I32(_) => builtin.int32,
            ast::IntLit::U32(_) => builtin.unsigned32,
            ast::IntLit::I64(_) => builtin.int64,
            ast::IntLit::U64(_) => builtin.unsigned64,
        }
    }

    fn lit_ty(&self, lit: &ast::PrimitiveLit) -> TyId {
        let builtin = &self.sema.tyck.builtin;

        match lit {
            ast::PrimitiveLit::Int(lit) => self.int_lit_ty(lit),

            ast::PrimitiveLit::Float(lit) => match lit {
                ast::FloatLit::F32(_) => builtin.float32,
                ast::FloatLit::F64(_) => builtin.float64,
            },

            ast::PrimitiveLit::String(_) => builtin.string,
            ast::PrimitiveLit::Char(_) => builtin.char,
            ast::PrimitiveLit::Bool(_) => builtin.bool,
            ast::PrimitiveLit::Null => builtin.null,
        }
    }

    fn check_lit_ty(
        &mut self,
        provenance: ConstrProvenance,
        lit: &ast::PrimitiveLit,
        expected: Option<TyId>,
    ) -> TyId {
        let ty_id = self.lit_ty(lit);

        self.check_ty(provenance, expected, ty_id)
    }

    fn repr(&self, ty_id: TyId) -> TyId {
        self.constrs.repr(ty_id)
    }

    fn fn_sig(&self, def_id: DefId) -> &FnSig {
        &self.sema.tyck.sigs[def_id]
    }

    fn check_ty_arg_arity(&mut self, loc: &Loc, expected: usize, actual: usize) -> bool {
        if expected > actual {
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(loc.clone())
                    .with_msg(format!(
                        "too many type arguments were provided: expected {expected}, got {actual}",
                    ))
                    .with_label(Label::primary(loc.clone()))
                    .build(),
            );

            false
        } else {
            true
        }
    }

    fn check_arg_arity(&mut self, loc: &Loc, expected: usize, actual: usize) {
        if expected != actual {
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(loc.clone())
                    .with_msg(format!(
                        "foo {quantifier} type arguments were provided: expected {expected}, got {actual}",
                        quantifier = if expected < actual { "many" } else { "few" },
                    ))
                    .with_label(Label::primary(loc.clone()))
                    .build()
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_enum_value_ty(
        &mut self,
        error_reported: &mut bool,
        enum_loc: &Loc,
        prev: &IntCtor,
        prev_variant: &'ast ast::EnumVariant,
        ctor: &IntCtor,
        ty_id: TyId,
        variant: &'ast ast::EnumVariant,
    ) -> (IntCtor, &'ast ast::EnumVariant) {
        if !*error_reported && prev.signed != ctor.signed {
            let prev_ty_id = self.int_ctor_ty(prev);

            *error_reported = true;
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(enum_loc.clone())
                    .with_msg(format!(
                        "could not infer an underlying type for this enum: `{}` and `{}` are incompatible",
                        self.sema.format_ty(prev_ty_id),
                        self.sema.format_ty(ty_id),
                    ))
                    .with_label(Label::primary(variant.value_loc.clone()).with_msg(format!(
                        "this expression has type `{}`",
                        self.sema.format_ty(ty_id),
                    )))
                    .with_label(Label::secondary(prev_variant.value_loc.clone()).with_msg(
                        format!(
                            "this expression has type `{}`",
                            self.sema.format_ty(prev_ty_id)
                        ),
                    ))
                    .build(),
            );

            (prev.clone(), prev_variant)
        } else {
            let signed = ctor.signed;
            let (width, variant) = if prev.width < ctor.width {
                (ctor.width, variant)
            } else {
                (prev.width, prev_variant)
            };

            (IntCtor { signed, width }, variant)
        }
    }

    fn make_fresh_vars_for_ty_params(
        &mut self,
        generics: &[TyId],
        loc: &Loc,
    ) -> SparseSecondaryMap<TyId, TyId> {
        generics
            .iter()
            .map(|&generic| {
                (
                    generic,
                    self.fresh_var(VarProvenance::Generic(generic, loc.clone())),
                )
            })
            .collect::<SparseSecondaryMap<_, _>>()
    }
}

// The early type-checking phase: initializes type constructors to allow type-checking type
// expressions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn early_tyck_decls(&mut self) {
        for file in self.sema.libsl.files.values() {
            for &decl_id in &file.decls {
                self.early_tyck_decl(decl_id);
            }
        }
    }

    fn early_tyck_decl(&mut self, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),
            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}
            ast::DeclKind::SemanticTy(d) => self.early_tyck_decl_semantic_ty(decl, d),
            ast::DeclKind::TyAlias(d) => self.early_tyck_decl_ty_alias(decl, d),
            ast::DeclKind::Struct(d) => self.early_tyck_decl_struct(decl, d),
            ast::DeclKind::Enum(d) => self.early_tyck_decl_enum(decl, d),
            ast::DeclKind::Annotation(d) => self.early_tyck_decl_annotation(decl, d),
            ast::DeclKind::Action(d) => self.early_tyck_decl_action(decl, d),
            ast::DeclKind::Automaton(d) => self.early_tyck_decl_automaton(decl, d),
            ast::DeclKind::Function(d) => self.early_tyck_decl_function(decl, d),
            ast::DeclKind::Variable(d) => self.early_tyck_decl_variable(decl, d),
            ast::DeclKind::State(d) => self.early_tyck_decl_state(decl, d),
            ast::DeclKind::Shift(d) => self.early_tyck_decl_shift(decl, d),
            ast::DeclKind::Constructor(d) => self.early_tyck_decl_constructor(decl, d),
            ast::DeclKind::Destructor(d) => self.early_tyck_decl_destructor(decl, d),
            ast::DeclKind::Proc(d) => self.early_tyck_decl_proc(decl, d),
        }
    }

    fn early_tyck_decl_semantic_ty(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclSemanticTy) {
        unimplemented!()
    }

    fn early_tyck_decl_ty_alias(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclTyAlias) {
        unimplemented!()
    }

    fn early_tyck_decl_struct(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(
            def_id,
            |def: &DefStruct| &def.generics,
            &d.ty_name.generics,
        );

        for &decl_id in &d.decls {
            self.early_tyck_decl(decl_id);
        }
    }

    fn early_tyck_decl_enum(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclEnum) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(
            def_id,
            |def: &DefEnum| &def.generics,
            &d.ty_name.generics,
        );
    }

    fn early_tyck_decl_annotation(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAnnotation) {
        // do nothing.
    }

    fn early_tyck_decl_action(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(def_id, |def: &DefAction| &def.generics, &d.generics);
    }

    fn early_tyck_decl_automaton(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(
            def_id,
            |def: &DefAutomaton| &def.generics,
            &d.name.generics,
        );

        for &decl_id in iter::chain(&d.constructor_variables, &d.decls) {
            self.early_tyck_decl(decl_id);
        }
    }

    fn early_tyck_decl_function(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(def_id, |def: &DefFunction| &def.generics, &d.generics);
    }

    fn early_tyck_decl_variable(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclVariable) {
        // do nothing.
    }

    fn early_tyck_decl_state(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn early_tyck_decl_shift(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclShift) {
        // do nothing.
    }

    fn early_tyck_decl_constructor(
        &mut self,
        decl: &'ast ast::Decl,
        d: &'ast ast::DeclConstructor,
    ) {
        // do nothing.
    }

    fn early_tyck_decl_destructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        // do nothing.
    }

    fn early_tyck_decl_proc(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.register_parametrized_entity(def_id, |def: &DefFunction| &def.generics, &d.generics);
    }

    fn register_parametrized_entity<T: DefKindProject>(
        &mut self,
        def_id: DefId,
        generics: impl FnOnce(&T) -> &[DefId],
        generic_decls: &[ast::Generic],
    ) {
        let def: &T = self.sema.name_res.def(def_id);
        let generics = generics(def);

        debug_assert_eq!(generics.len(), generic_decls.len());

        for &generic in generics {
            let ty_id = self.sema.tyck.make_param_for(&self.sema.name_res, generic);
            self.sema.tyck.def_tys.insert(generic, ty_id);
        }

        self.sema.tyck.param_variances.insert(
            def_id,
            generic_decls
                .iter()
                .map(|generic| generic.variance.clone().unwrap_or(Variance::Invariant))
                .collect(),
        );
    }
}

// The declaration type-checking phase: assigns types to globally visible entities, such as
// variables and functions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_decls(&mut self) {
        for file in self.sema.libsl.files.values() {
            for &decl_id in &file.decls {
                self.tyck_decl(decl_id);
            }
        }
    }

    fn tyck_decl(&mut self, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),
            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}
            ast::DeclKind::SemanticTy(d) => self.tyck_decl_semantic_ty(decl, d),
            ast::DeclKind::TyAlias(d) => self.tyck_decl_ty_alias(decl, d),
            ast::DeclKind::Struct(d) => self.tyck_decl_struct(decl, d),
            ast::DeclKind::Enum(d) => self.tyck_decl_enum(decl, d),
            ast::DeclKind::Annotation(d) => self.tyck_decl_annotation(decl, d),
            ast::DeclKind::Action(d) => self.tyck_decl_action(decl, d),
            ast::DeclKind::Automaton(d) => self.tyck_decl_automaton(decl, d),
            ast::DeclKind::Function(d) => self.tyck_decl_function(decl, d),
            ast::DeclKind::Variable(d) => self.tyck_decl_variable(decl, d),
            ast::DeclKind::State(d) => self.tyck_decl_state(decl, d),
            ast::DeclKind::Shift(d) => self.tyck_decl_shift(decl, d),
            ast::DeclKind::Constructor(d) => self.tyck_decl_constructor(decl, d),
            ast::DeclKind::Destructor(d) => self.tyck_decl_destructor(decl, d),
            ast::DeclKind::Proc(d) => self.tyck_decl_proc(decl, d),
        }
    }

    fn tyck_decl_semantic_ty(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclSemanticTy) {
        unimplemented!()
    }

    fn tyck_decl_ty_alias(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclTyAlias) {
        unimplemented!()
    }

    fn tyck_decl_struct(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        for &decl_id in &d.decls {
            self.tyck_decl(decl_id);
        }
    }

    fn tyck_decl_enum(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclEnum) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        let mut common_ty: Option<(IntCtor, &ast::EnumVariant)> = None;
        let mut error_reported = false;

        for variant in &d.variants {
            let ty_id = self.int_lit_ty(&variant.value);
            let ctor = self.sema.tyck.tys[ty_id].as_constructed().unwrap().ctor;
            let ctor = self
                .sema
                .name_res
                .def::<BuiltinTyCtor>(ctor)
                .as_int()
                .unwrap()
                .clone();

            common_ty = Some(if let Some(common_ty) = common_ty {
                let (prev, prev_variant) = &common_ty;

                self.check_enum_value_ty(
                    &mut error_reported,
                    &d.ty_name.ty_name.loc,
                    prev,
                    prev_variant,
                    &ctor,
                    ty_id,
                    variant,
                )
            } else {
                (ctor, variant)
            });
        }

        let common_ty = common_ty.map_or_else(
            || self.sema.tyck.builtin.int32,
            |(ctor, _)| self.int_ctor_ty(&ctor),
        );

        self.sema.tyck.underlying_tys.insert(def_id, common_ty);

        for &variant in &self.sema.name_res.def::<DefEnum>(def_id).variants {
            self.sema.tyck.def_tys.insert(variant, common_ty);
        }
    }

    fn tyck_decl_annotation(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAnnotation) {
        let def_id = self.sema.name_res.decl_defs[decl.id];

        self.tyck_params(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            |def: &DefAnnotation| &def.params,
        );

        self.register_fn_sig::<DefAnnotation>(def_id, None, |_| &[], |def| &def.params, None);
    }

    fn tyck_decl_action(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        let def_id = self.sema.name_res.decl_defs[decl.id];

        self.tyck_params(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            |def: &DefAction| &def.params,
        );

        let ret = self.tyck_ret_ty_expr(d.ret_ty_expr);
        self.register_fn_sig::<DefAction>(
            def_id,
            None,
            |def| &def.generics,
            |def| &def.params,
            Some(ret),
        );
    }

    fn tyck_decl_automaton(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        let def_id = self.sema.name_res.decl_defs[decl.id];

        for &decl_id in &d.constructor_variables {
            self.tyck_decl(decl_id);
        }

        let underlying = self.tyck_ty_expr(d.ty_expr);
        self.sema.tyck.underlying_tys.insert(def_id, underlying);

        let def = self.sema.name_res.def::<DefAutomaton>(def_id);
        let ty_params = def
            .generics
            .iter()
            .map(|&def_id| self.sema.tyck.def_tys[def_id])
            .collect::<Vec<_>>();
        let ty_id = self.sema.tyck.add_ctor_ty(def_id, ty_params.clone());

        self.sema.tyck.sigs.insert(
            def_id,
            FnSig {
                recv: None,
                generics: ty_params,
                params: vec![underlying],
                ret: Some(ty_id),
            },
        );

        for &decl_id in &d.decls {
            self.tyck_decl(decl_id);
        }
    }

    fn tyck_decl_function(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.tyck_fn_decl(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            d.ret_ty_expr,
        );
    }

    fn tyck_decl_variable(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclVariable) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        let ty_id = self.tyck_ty_expr(d.ty_expr);
        self.sema.tyck.def_tys.insert(def_id, ty_id);
    }

    fn tyck_decl_state(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn tyck_decl_shift(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclShift) {
        // do nothing.
    }

    fn tyck_decl_constructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclConstructor) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.tyck_fn_decl(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            d.ret_ty_expr,
        );
    }

    fn tyck_decl_destructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.tyck_fn_decl(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            d.ret_ty_expr,
        );
    }

    fn tyck_decl_proc(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        self.tyck_fn_decl(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            d.ret_ty_expr,
        );
    }

    fn tyck_ty_expr(&mut self, ty_expr_id: TyExprId) -> TyId {
        let ty_expr = &self.sema.libsl.ty_exprs[ty_expr_id];

        match &ty_expr.kind {
            ast::TyExprKind::Dummy => unreachable!(),
            ast::TyExprKind::PrimitiveLit(t) => self.tyck_ty_expr_primitive_lit(ty_expr, t),
            ast::TyExprKind::Name(t) => self.tyck_ty_expr_name(ty_expr, t),
            ast::TyExprKind::Pointer(t) => self.tyck_ty_expr_pointer(ty_expr, t),
            ast::TyExprKind::Intersection(t) => self.tyck_ty_expr_intersection(ty_expr, t),
            ast::TyExprKind::Union(t) => self.tyck_ty_expr_union(ty_expr, t),
        }

        self.sema.tyck.ty_exprs[ty_expr_id]
    }

    fn tyck_ty_expr_primitive_lit(
        &mut self,
        ty_expr: &'ast ast::TyExpr,
        t: &'ast ast::TyExprPrimitiveLit,
    ) {
        let ty_id = self.lit_ty(&t.lit);
        self.sema.tyck.ty_exprs.insert(ty_expr.id, ty_id);
    }

    fn tyck_ty_expr_name(&mut self, ty_expr: &'ast ast::TyExpr, t: &'ast ast::TyExprName) {
        let ty_args = t
            .generics
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|arg| self.tyck_ty_arg(arg))
            .collect::<Vec<_>>();

        let def_id = self.sema.name_res.ty_expr_names[ty_expr.id];
        let def_id = self.sema.name_res.resolve_import(def_id);

        match &self.sema.name_res.defs[def_id].kind {
            DefKind::Dummy => unreachable!(),
            DefKind::Import(_) => unreachable!(),
            DefKind::BuiltinCtor(_) => {}
            DefKind::SemanticTy(_) => {}
            DefKind::SemanticTyEnumValue { .. } => unreachable!(),
            DefKind::TyAlias(_) => {
                return self.tyck_ty_expr_name_alias(ty_expr, t, ty_args, def_id);
            }
            DefKind::Struct(_) => {}
            DefKind::Enum(_) => {}
            DefKind::EnumVariant { .. } => unreachable!(),
            DefKind::Annotation(_) => unreachable!(),
            DefKind::Action(_) => unreachable!(),
            DefKind::Automaton(_) => {}
            DefKind::Function(_) => unreachable!(),
            DefKind::Variable(_) => unreachable!(),
            DefKind::State(_) => unreachable!(),
            DefKind::TyVariable(_) => {
                return self.tyck_ty_expr_name_ty_var(ty_expr, t, ty_args, def_id);
            }
            DefKind::Param { .. } => unreachable!(),
            DefKind::Pred(_) => unreachable!(),
        }

        if !self.check_ty_arg_arity(
            &ty_expr.loc,
            self.sema.tyck.param_variances[def_id].len(),
            ty_args.len(),
        ) {
            self.sema
                .tyck
                .ty_exprs
                .insert(ty_expr.id, self.sema.tyck.builtin.error);

            return;
        }

        // TODO: constraints.
        let ty_id = self.sema.tyck.add_ctor_ty(def_id, ty_args);
        self.sema.tyck.ty_exprs.insert(ty_expr.id, ty_id);
    }

    fn tyck_ty_expr_name_alias(
        &mut self,
        ty_expr: &'ast ast::TyExpr,
        t: &'ast ast::TyExprName,
        ty_args: Vec<TyId>,
        def_id: DefId,
    ) {
        unimplemented!()
    }

    fn tyck_ty_expr_name_ty_var(
        &mut self,
        ty_expr: &'ast ast::TyExpr,
        _t: &'ast ast::TyExprName,
        ty_args: Vec<TyId>,
        def_id: DefId,
    ) {
        if !ty_args.is_empty() {
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(ty_expr.loc.clone())
                    .with_msg("type parameter cannot have type arguments")
                    .with_label(
                        Label::primary(ty_expr.loc.clone()).with_msg("refers to a type parameter"),
                    )
                    .build(),
            );

            self.sema
                .tyck
                .ty_exprs
                .insert(ty_expr.id, self.sema.tyck.builtin.error);

            return;
        }

        let ty_id = self.sema.tyck.def_tys[def_id];
        self.sema.tyck.ty_exprs.insert(ty_expr.id, ty_id);
    }

    fn tyck_ty_expr_pointer(&mut self, ty_expr: &'ast ast::TyExpr, t: &'ast ast::TyExprPointer) {
        let base = self.tyck_ty_expr(t.base);
        let ty_id = self
            .sema
            .tyck
            .add_ctor_ty(self.sema.name_res.prelude_defs.pointer, vec![base]);
        self.sema.tyck.ty_exprs.insert(ty_expr.id, ty_id);
    }

    fn tyck_ty_expr_intersection(
        &mut self,
        ty_expr: &'ast ast::TyExpr,
        t: &'ast ast::TyExprIntersection,
    ) {
        unimplemented!()
    }

    fn tyck_ty_expr_union(&mut self, ty_expr: &'ast ast::TyExpr, t: &'ast ast::TyExprUnion) {
        unimplemented!()
    }

    fn tyck_ret_ty_expr(&mut self, ret_ty_expr: Option<TyExprId>) -> TyId {
        match ret_ty_expr {
            Some(ty_expr_id) => self.tyck_ty_expr(ty_expr_id),
            None => self.sema.tyck.builtin.void,
        }
    }

    fn tyck_params<T: DefKindProject>(
        &mut self,
        def_id: DefId,
        param_ty_exprs: impl Iterator<Item = TyExprId>,
        param_defs: impl FnOnce(&T) -> &[DefId],
    ) {
        let param_tys = param_ty_exprs
            .map(|ty_expr_id| self.tyck_ty_expr(ty_expr_id))
            .collect::<Vec<_>>();

        let def: &T = self.sema.name_res.def(def_id);

        for (&param_def_id, ty_id) in iter::zip(param_defs(def), param_tys) {
            self.sema.tyck.def_tys.insert(param_def_id, ty_id);
        }
    }

    fn register_fn_sig<T: DefKindProject>(
        &mut self,
        def_id: DefId,
        recv: Option<DefId>,
        generics: impl FnOnce(&T) -> &[DefId],
        params: impl FnOnce(&T) -> &[DefId],
        ret: Option<TyId>,
    ) {
        let def = self.sema.name_res.def(def_id);
        let generics = generics(def);
        let params = params(def);

        let generics = generics
            .iter()
            .map(|&generic| self.sema.tyck.def_tys[generic])
            .collect();
        let params = params
            .iter()
            .map(|&param| self.sema.tyck.def_tys[param])
            .collect();

        self.sema.tyck.sigs.insert(
            def_id,
            FnSig {
                recv,
                generics,
                params,
                ret,
            },
        );
    }

    fn tyck_fn_decl(
        &mut self,
        def_id: DefId,
        param_ty_exprs: impl Iterator<Item = TyExprId>,
        ret: Option<TyExprId>,
    ) {
        let recv = match self.sema.name_res.def::<DefFunction>(def_id).kind {
            FunctionKind::Fun { of } => of,
            FunctionKind::Proc { of, .. } => of,
            FunctionKind::Constructor { of } => Some(of),
            FunctionKind::Destructor { of } => Some(of),
        };

        self.tyck_params(def_id, param_ty_exprs, |def: &DefFunction| &def.params);
        let ret = self.tyck_ret_ty_expr(ret);
        self.register_fn_sig::<DefFunction>(
            def_id,
            recv,
            |def| &def.generics,
            |def| &def.params,
            Some(ret),
        );
    }
}

// The main type-checking phase.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_decl_bodies(&mut self) {
        for file in self.sema.libsl.files.values() {
            for &decl_id in &file.decls {
                self.tyck_decl_body(decl_id);
            }
        }
    }

    fn tyck_decl_body(&mut self, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),
            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}
            ast::DeclKind::SemanticTy(d) => self.tyck_decl_semantic_ty_body(decl, d),
            ast::DeclKind::TyAlias(d) => self.tyck_decl_ty_alias_body(decl, d),
            ast::DeclKind::Struct(d) => self.tyck_decl_struct_body(decl, d),
            ast::DeclKind::Enum(d) => self.tyck_decl_enum_body(decl, d),
            ast::DeclKind::Annotation(d) => self.tyck_decl_annotation_body(decl, d),
            ast::DeclKind::Action(d) => self.tyck_decl_action_body(decl, d),
            ast::DeclKind::Automaton(d) => self.tyck_decl_automaton_body(decl, d),
            ast::DeclKind::Function(d) => self.tyck_decl_function_body(decl, d),
            ast::DeclKind::Variable(d) => self.tyck_decl_variable_body(decl, d),
            ast::DeclKind::State(d) => self.tyck_decl_state_body(decl, d),
            ast::DeclKind::Shift(d) => self.tyck_decl_shift_body(decl, d),
            ast::DeclKind::Constructor(d) => self.tyck_decl_constructor_body(decl, d),
            ast::DeclKind::Destructor(d) => self.tyck_decl_destructor_body(decl, d),
            ast::DeclKind::Proc(d) => self.tyck_decl_proc_body(decl, d),
        }
    }

    fn tyck_expr(&mut self, expr_id: ExprId, expected: Option<TyId>) -> TyId {
        let expr = &self.sema.libsl.exprs[expr_id];

        match &expr.kind {
            ast::ExprKind::Dummy => unreachable!(),
            ast::ExprKind::PrimitiveLit(e) => self.tyck_expr_primitive_lit(expr, e, expected),
            ast::ExprKind::ArrayLit(e) => self.tyck_expr_array_lit(expr, e, expected),
            ast::ExprKind::SetLit(e) => self.tyck_expr_set_lit(expr, e, expected),
            ast::ExprKind::Access(e) => self.tyck_expr_access(expr, e, expected),
            ast::ExprKind::Prev(e) => self.tyck_expr_prev(expr, e, expected),
            ast::ExprKind::ProcCall(e) => self.tyck_expr_proc_call(expr, e, expected),
            ast::ExprKind::ActionCall(e) => self.tyck_expr_action_call(expr, e, expected),
            ast::ExprKind::Instantiate(e) => self.tyck_expr_instantiate(expr, e, expected),
            ast::ExprKind::HasConcept(e) => self.tyck_expr_has_concept(expr, e, expected),
            ast::ExprKind::Cast(e) => self.tyck_expr_cast(expr, e, expected),
            ast::ExprKind::TyCompare(e) => self.tyck_expr_ty_compare(expr, e, expected),
            ast::ExprKind::Unary(e) => self.tyck_expr_unary(expr, e, expected),
            ast::ExprKind::Binary(e) => self.tyck_expr_binary(expr, e, expected),
        }

        self.sema.tyck.exprs[expr_id]
    }

    fn tyck_access(&mut self, access_id: AccessId, expected: Option<TyId>) -> TyId {
        let access = &self.sema.libsl.accesses[access_id];
        todo!();

        self.sema.tyck.accesses[access_id]
    }

    fn check_ty(
        &mut self,
        provenance: ConstrProvenance,
        expected: Option<TyId>,
        actual: TyId,
    ) -> TyId {
        if let Some(expected) = expected {
            if self.constr_coerce(actual, expected, provenance).is_ok() {
                self.repr(expected)
            } else {
                self.sema.tyck.builtin.error
            }
        } else {
            actual
        }
    }

    fn tyck_ty_arg(&mut self, ty_arg: &'ast ast::TyArg) -> TyId {
        match ty_arg {
            ast::TyArg::TyExpr(variance, ty_expr_id) => {
                let ty_id = self.tyck_ty_expr(*ty_expr_id);

                match variance {
                    Some(ast::Variance::Invariant) | None => ty_id,

                    Some(ast::Variance::Covariant) => todo!(),
                    Some(ast::Variance::Contravariant) => todo!(),
                }
            }

            ast::TyArg::Wildcard(_) => todo!(),
        }
    }

    fn tyck_op_expr<O: Op>(
        &mut self,
        expr: &'ast ast::Expr,
        expected: Option<TyId>,
        op: O,
        args: &[TyId],
        mut candidates: Vec<OpFnSigProvider<O>>,
    ) {
        candidates
            .retain(|candidate| self.is_function_applicable(candidate, &Receiver::None, args, &[]));

        let Ok(overload) =
            self.select_overload(&candidates, &OpOverloadDiagProvider::new(op, &expr.loc))
        else {
            self.sema
                .tyck
                .exprs
                .insert(expr.id, self.sema.tyck.builtin.error);

            return;
        };

        let sig = overload.fn_sig();
        let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &expr.loc);

        for (&param, &arg) in iter::zip(&sig.params, args) {
            let param = self.sema.tyck.subst(param, &ty_param_map);
            let _ = self.constr_coerce(arg, param, ConstrProvenance::Expr(expr.id));
        }

        let ret = self.sema.tyck.subst(sig.ret.unwrap(), &ty_param_map);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ret);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn make_missing_constructor_args_err(loc: Loc, missing_args: &[String]) -> Diag {
        Diag::err()
            .at(loc.clone())
            .with_msg(match missing_args {
                [] => unreachable!(),
                [name] => {
                    format!("no argument initializes the constructor parameter `{name}`")
                }

                _ => {
                    let mut msg = "no arguments initialize the constructor parameters ".to_owned();

                    for (idx, name) in missing_args.iter().enumerate() {
                        if idx > 0 && !(idx == 1 && missing_args.len() == 2) {
                            let _ = write!(msg, ", ");
                        }

                        if idx + 1 == missing_args.len() {
                            let _ = write!(msg, "and ");
                        }

                        let _ = write!(msg, "{name}");
                    }

                    msg
                }
            })
            .with_label(Label::primary(loc))
            .build()
    }
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_decl_semantic_ty_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclSemanticTy) {
        unimplemented!()
    }

    fn tyck_decl_ty_alias_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclTyAlias) {
        unimplemented!()
    }

    fn tyck_decl_struct_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        // TODO: annotations.
        for &decl_id in &d.decls {
            self.tyck_decl_body(decl_id);
        }
    }

    fn tyck_decl_enum_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclEnum) {
        // TODO: annotations.
    }

    fn tyck_decl_annotation_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAnnotation) {
        let def_id = self.sema.name_res.decl_defs[decl.id];
        let param_tys = self
            .sema
            .name_res
            .def::<DefAnnotation>(def_id)
            .params
            .iter()
            .map(|&param| self.sema.tyck.def_tys[param])
            .collect::<Vec<_>>();

        for (param, ty_id) in iter::zip(&d.params, param_tys) {
            if let Some(expr_id) = param.default {
                self.tyck_expr(expr_id, Some(ty_id));
            }
        }
    }

    fn tyck_decl_action_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        // TODO: annotations.
    }

    fn tyck_decl_automaton_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        // TODO: annotations.
        for &decl_id in iter::chain(&d.constructor_variables, &d.decls) {
            self.tyck_decl_body(decl_id);
        }
    }

    fn tyck_decl_function_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_decl_variable_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclVariable) {
        // TODO: annotations.
        if let Some(expr_id) = d.init {
            let def_id = self.sema.name_res.decl_defs[decl.id];
            let ty_id = self.sema.tyck.def_tys[def_id];
            self.tyck_expr(expr_id, Some(ty_id));
        }
    }

    fn tyck_decl_state_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn tyck_decl_shift_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclShift) {
        // TODO: resolve overloads.
    }

    fn tyck_decl_constructor_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclConstructor) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_decl_destructor_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_decl_proc_body(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_function_body(&mut self, body: &'ast ast::FunctionBody) {
        for contract in &body.contracts {
            self.tyck_contract(contract);
        }

        for &stmt_id in &body.stmts {
            self.tyck_stmt(stmt_id);
        }
    }

    fn tyck_contract(&mut self, contract: &'ast ast::Contract) {
        match contract {
            ast::Contract::Requires(contract) => self.tyck_contract_requires(contract),
            ast::Contract::Ensures(contract) => self.tyck_contract_ensures(contract),
            ast::Contract::Assigns(contract) => self.tyck_contract_assigns(contract),
        }
    }

    fn tyck_contract_requires(&mut self, contract: &'ast ast::ContractRequires) {
        self.tyck_pred(contract.pred);
    }

    fn tyck_contract_ensures(&mut self, contract: &'ast ast::ContractEnsures) {
        self.tyck_pred(contract.pred);
    }

    fn tyck_contract_assigns(&mut self, contract: &'ast ast::ContractAssigns) {
        unimplemented!()
    }

    fn tyck_stmt(&mut self, stmt_id: StmtId) {
        let stmt = &self.sema.libsl.stmts[stmt_id];

        match &stmt.kind {
            ast::StmtKind::Dummy => todo!(),
            ast::StmtKind::Decl(decl_id) => self.tyck_stmt_decl(stmt, *decl_id),
            ast::StmtKind::If(s) => self.tyck_stmt_if(stmt, s),
            ast::StmtKind::Assign(s) => self.tyck_stmt_assign(stmt, s),
            ast::StmtKind::Cancel(s) => self.tyck_stmt_cancel(stmt, s),
            ast::StmtKind::Expr(expr_id) => self.tyck_stmt_expr(stmt, *expr_id),
        }
    }

    fn tyck_stmt_decl(&mut self, stmt: &'ast ast::Stmt, decl_id: DeclId) {
        self.early_tyck_decl(decl_id);
        self.tyck_decl(decl_id);
        self.tyck_decl_body(decl_id);
    }

    fn tyck_stmt_if(&mut self, stmt: &'ast ast::Stmt, s: &'ast ast::StmtIf) {
        self.tyck_expr(s.cond, Some(self.sema.tyck.builtin.bool));

        for &stmt_id in iter::chain(&s.then_branch, &s.else_branch) {
            self.tyck_stmt(stmt_id);
        }
    }

    fn tyck_stmt_assign(&mut self, stmt: &'ast ast::Stmt, s: &'ast ast::StmtAssign) {
        todo!()
    }

    fn tyck_stmt_cancel(&mut self, stmt: &'ast ast::Stmt, s: &'ast ast::StmtCancel) {
        let enclosing_fn_def_id = self.sema.name_res.stmts[stmt.id].enclosing_fn;
        let enclosing_fn = self.sema.name_res.def::<DefFunction>(enclosing_fn_def_id);

        if let FunctionKind::Fun { of } = enclosing_fn.kind
            && let Some(of) = of
            && let DefKind::Automaton(_) = self.sema.name_res.defs[of].kind
        {
            // allowed.
        } else {
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(stmt.loc.clone())
                    .with_msg("cancel statement is only allowed in automaton functions")
                    .with_label(Label::primary(stmt.loc.clone()))
                    .build(),
            );
        }
    }

    fn tyck_stmt_expr(&mut self, stmt: &'ast ast::Stmt, expr_id: ExprId) {
        self.tyck_expr(expr_id, None);
    }

    fn tyck_pred(&mut self, pred_id: PredId) {
        todo!()
    }

    fn tyck_expr_primitive_lit(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprPrimitiveLit,
        expected: Option<TyId>,
    ) {
        let ty_id = self.check_lit_ty(ConstrProvenance::Expr(expr.id), &e.lit, expected);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_array_lit(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprArrayLit,
        expected: Option<TyId>,
    ) {
        let elem_ty_id = self.fresh_var(VarProvenance::Element { of: expr.id });

        for &elem in &e.elems {
            self.tyck_expr(elem, Some(elem_ty_id));
        }

        let ty_id = self
            .sema
            .tyck
            .add_ctor_ty(self.sema.name_res.prelude_defs.array, vec![elem_ty_id]);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_set_lit(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprSetLit,
        expected: Option<TyId>,
    ) {
        let elem_ty_id = self.fresh_var(VarProvenance::Element { of: expr.id });

        for &elem in &e.elems {
            self.tyck_expr(elem, Some(elem_ty_id));
        }

        let ty_id = self
            .sema
            .tyck
            .add_ctor_ty(self.sema.name_res.prelude_defs.set, vec![elem_ty_id]);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_access(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprAccess,
        expected: Option<TyId>,
    ) {
        let ty_id = self.tyck_access(e.access, expected);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_prev(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprPrev,
        expected: Option<TyId>,
    ) {
        // TODO: ensure well-formedness.
        let ty_id = self.tyck_access(e.access, expected);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_proc_call(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprProcCall,
        expected: Option<TyId>,
    ) {
        let ty_args = e
            .generics
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|ty_arg| self.tyck_ty_arg(ty_arg))
            .collect::<Vec<_>>();

        let args = e
            .args
            .iter()
            .copied()
            .map(|arg| self.tyck_expr(arg, None))
            .collect::<Vec<_>>();

        let Ok((recv, def_id)) = self.resolve_callee(e.callee, &args, &ty_args) else {
            self.sema
                .tyck
                .exprs
                .insert(expr.id, self.sema.tyck.builtin.error);

            return;
        };

        self.check_ty_arg_arity(&expr.loc, ty_args.len(), self.fn_sig(def_id).generics.len());
        self.check_arg_arity(&expr.loc, args.len(), self.fn_sig(def_id).params.len());

        let sig = self.fn_sig(def_id).clone();
        let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &expr.loc);

        for (&param, &arg) in iter::zip(&sig.generics, &ty_args) {
            let _ = self.constr_eq(arg, ty_param_map[param], ConstrProvenance::Expr(expr.id));
        }

        match sig.recv {
            Some(_) => todo!(),
            None => {}
        }

        for (&param, &arg) in iter::zip(&sig.params, &args) {
            let param = self.sema.tyck.subst(param, &ty_param_map);
            let _ = self.constr_coerce(arg, param, ConstrProvenance::Expr(expr.id));
        }

        let ret = self.sema.tyck.subst(sig.ret.unwrap(), &ty_param_map);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ret);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_action_call(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprActionCall,
        expected: Option<TyId>,
    ) {
        // TODO: deduplicate.
        let ty_args = e
            .generics
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|ty_arg| self.tyck_ty_arg(ty_arg))
            .collect::<Vec<_>>();

        let args = e
            .args
            .iter()
            .copied()
            .map(|arg| self.tyck_expr(arg, None))
            .collect::<Vec<_>>();

        let def_id = self.sema.name_res.expr_action_calls[expr.id];

        self.check_ty_arg_arity(&expr.loc, ty_args.len(), self.fn_sig(def_id).generics.len());
        self.check_arg_arity(&expr.loc, args.len(), self.fn_sig(def_id).params.len());

        let sig = self.fn_sig(def_id).clone();
        let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &expr.loc);

        for (&param, &arg) in iter::zip(&sig.generics, &ty_args) {
            let _ = self.constr_eq(arg, ty_param_map[param], ConstrProvenance::Expr(expr.id));
        }

        for (&param, &arg) in iter::zip(&sig.params, &args) {
            let param = self.sema.tyck.subst(param, &ty_param_map);
            let _ = self.constr_coerce(arg, param, ConstrProvenance::Expr(expr.id));
        }

        let ret = self.sema.tyck.subst(sig.ret.unwrap(), &ty_param_map);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ret);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_instantiate(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprInstantiate,
        expected: Option<TyId>,
    ) {
        let automaton_def_id = self.sema.name_res.expr_instantiations[expr.id].automaton;

        let ty_args = e
            .generics
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|ty_arg| self.tyck_ty_arg(ty_arg))
            .collect::<Vec<_>>();

        type ArgState<'a, T> = Result<(&'a ast::ConstructorArg, T), Diag>;

        let mut args: SparseSecondaryMap<DefId, ArgState<_>> = Default::default();
        let mut state: Option<ArgState<DefId>> = None;

        for (idx, arg) in e.args.iter().enumerate() {
            match arg {
                ast::ConstructorArg::State(loc, _) => {
                    let diag = match state {
                        Some(Ok((prev, _))) => {
                            self.result = Err(());
                            state
                                .insert(Err(Diag::err()
                                    .at(prev.loc().clone())
                                    .with_msg("too many state arguments were provided")
                                    .with_label(Label::primary(prev.loc().clone()))
                                    .build()))
                                .as_mut()
                                .unwrap_err()
                        }

                        Some(Err(ref mut diag)) => diag,

                        None => {
                            let info = &self.sema.name_res.expr_instantiations[expr.id];
                            state = Some(Ok((arg, info.args[idx])));

                            continue;
                        }
                    };

                    diag.labels.push(Label::primary(loc.clone()));
                }

                ast::ConstructorArg::Var(loc, _, expr_id) => {
                    use slotmap::sparse_secondary::Entry;

                    let ty_id = self.tyck_expr(*expr_id, None);
                    let info = &self.sema.name_res.expr_instantiations[expr.id];

                    match args.entry(info.args[idx]).unwrap() {
                        Entry::Vacant(entry) => {
                            entry.insert(Ok((arg, ty_id)));
                        }

                        Entry::Occupied(mut entry) => {
                            let diag = match entry.get_mut() {
                                r @ &mut Ok((prev, _)) => {
                                    self.result = Err(());
                                    *r = Err(Diag::err()
                                        .at(prev.loc().clone())
                                        .with_msg(
                                            "constructor parameter is initialized more than once",
                                        )
                                        .with_label(Label::primary(prev.loc().clone()))
                                        .build());

                                    r.as_mut().unwrap_err()
                                }

                                Err(diag) => diag,
                            };

                            diag.labels.push(Label::primary(loc.clone()));
                        }
                    }
                }
            }
        }

        let def = self.sema.name_res.def::<DefAutomaton>(automaton_def_id);
        let mut missing_args = vec![];
        let args = def
            .constructor_params
            .iter()
            .map(|&def_id| match args.remove(def_id) {
                Some(Ok((_, ty_id))) => (def_id, ty_id),

                Some(Err(diag)) => {
                    self.diag.emit(diag);

                    Default::default()
                }

                None => {
                    missing_args.push(self.sema.name_res.defs[def_id].name.clone());

                    Default::default()
                }
            })
            .collect::<Vec<_>>();

        if !missing_args.is_empty() {
            self.result = Err(());
            self.diag.emit(Self::make_missing_constructor_args_err(
                expr.loc.clone(),
                &missing_args,
            ));
        }

        match state {
            Some(Ok((arg, def_id))) => {
                if def.final_states.contains(&def_id) {
                    self.result = Err(());
                    self.diag.emit(
                        Diag::err()
                            .at(arg.loc().clone())
                            .with_msg(format_args!(
                                "state `{}` is declared as final and cannot be initial",
                                self.sema.name_res.defs[def_id].name,
                            ))
                            .with_label(Label::primary(arg.loc().clone()))
                            .build(),
                    );
                }
            }

            Some(Err(diag)) => {
                self.diag.emit(diag);
            }

            None => {
                self.result = Err(());
                self.diag.emit(
                    Diag::err()
                        .at(expr.loc.clone())
                        .with_msg("no initial state was provided")
                        .with_label(Label::primary(expr.loc.clone()))
                        .build(),
                );
            }
        }

        let generics = def
            .generics
            .iter()
            .map(|&def_id| self.sema.tyck.def_tys[def_id])
            .collect::<Vec<_>>();
        let ty_param_map = self.make_fresh_vars_for_ty_params(&generics, &expr.loc);

        for (&param, &arg) in iter::zip(&generics, &ty_args) {
            let _ = self.constr_eq(arg, ty_param_map[param], ConstrProvenance::Expr(expr.id));
        }

        for &(def_id, arg) in &args {
            let def_ty_id = self
                .sema
                .tyck
                .subst(self.sema.tyck.def_tys[def_id], &ty_param_map);
            let _ = self.constr_coerce(arg, def_ty_id, ConstrProvenance::Expr(expr.id));
        }

        let ty_args = generics.iter().map(|ty_arg| self.repr(*ty_arg)).collect();

        let ty_id = self.sema.tyck.add_ctor_ty(automaton_def_id, ty_args);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_has_concept(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprHasConcept,
        expected: Option<TyId>,
    ) {
        todo!()
    }

    fn tyck_expr_cast(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprCast,
        expected: Option<TyId>,
    ) {
        self.tyck_expr(e.expr, None);
        let ty_id = self.tyck_ty_expr(e.ty_expr);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_ty_compare(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprTyCompare,
        expected: Option<TyId>,
    ) {
        self.tyck_expr(e.expr, None);
        self.tyck_ty_expr(e.ty_expr);
        let ty_id = self.check_ty(
            ConstrProvenance::Expr(expr.id),
            expected,
            self.sema.tyck.builtin.bool,
        );
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_unary(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprUnary,
        expected: Option<TyId>,
    ) {
        let args = vec![self.tyck_expr(e.expr, None)];
        let candidates = self.overloads_for_unary(e.op, &expr.loc);

        self.tyck_op_expr(expr, expected, e.op, &args, candidates)
    }

    fn tyck_expr_binary(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprBinary,
        expected: Option<TyId>,
    ) {
        let args = vec![self.tyck_expr(e.lhs, None), self.tyck_expr(e.rhs, None)];
        let candidates = self.overloads_for_binary(e.op, &expr.loc);

        self.tyck_op_expr(expr, expected, e.op, &args, candidates)
    }
}
