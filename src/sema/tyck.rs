//! Type checking and inference for LibSL.

use std::collections::HashMap;
use std::fmt::{self, Display, Write};
use std::{iter, mem};

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap};

use crate::ast::Variance;
use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{
    Def, DefAction, DefAnnotation, DefAutomaton, DefFunction, DefId, DefKind, DefVariable,
    FunctionKind, VariableKind,
};
use crate::sema::resolve::{ExprCtxKind, Ns, ScopeId, ScopeKind};
use crate::sema::ty::{
    BuiltinTyCtor, ConstructedTy, FloatCtor, IntCtor, IntWidth, Ty, TyId, TyUnion,
};
use crate::sema::tyck::constraints::{ConstrProvenance, ConstrSet, VarProvenance};
use crate::sema::tyck::operators::{Op, OpFnSigProvider, OpOverload, OpOverloadDiagProvider};
use crate::sema::tyck::overload::Receiver;
use crate::sema::{Result, Sema};
use crate::{DeclId, ExprId, PredId, StmtId, TyExprId, ast};

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

#[derive(Debug, Clone)]
pub struct ResolvedName {
    pub kind: ResolvedNameKind,
    pub def_id: DefId,
}

#[derive(Debug, Clone)]
pub enum ResolvedNameKind {
    Var,
    ImplicitField,
}

#[derive(Debug, Clone)]
pub enum AssignmentKind {
    Var(DefId),
    Field { implicit: bool, def_id: DefId },
    Index,
}

#[derive(Debug, Clone, Copy)]
pub enum ReplaceTyArgs<'a> {
    Yes(&'a Loc),
    No,
}

#[derive(Debug, Default)]
pub struct TyCk {
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: HashMap<Ty, TyId>,
    pub builtin: BuiltinTys,
    pub exprs: SecondaryMap<ExprId, TyId>,
    pub ty_exprs: SecondaryMap<TyExprId, TyId>,

    // maps variables and generics to their types.
    pub def_tys: SecondaryMap<DefId, TyId>,

    pub sigs: SparseSecondaryMap<DefId, FnSig>,
    pub param_variances: SparseSecondaryMap<DefId, Vec<Variance>>,
    pub ty_params: Vec<TyParam>,
    pub operators: SparseSecondaryMap<ExprId, OpOverload>,
    pub assignments: SparseSecondaryMap<StmtId, AssignmentKind>,

    // maps procedure call expressions to their resolved call targets.
    pub call_targets: SparseSecondaryMap<ExprId, (Receiver, DefId)>,

    // maps name expressions to resolved entities.
    pub name_exprs: SparseSecondaryMap<ExprId, ResolvedName>,

    // maps field expressions to resolved fields.
    pub field_exprs: SparseSecondaryMap<ExprId, DefId>,

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

        Ty::Union(t) => {
            for &elem in &t.elems {
                occurrences.extend(&var_occurrences[elem]);
            }
        }
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

        Ty::Union(t) => {
            for &elem in &t.elems {
                let p = preds.entry(elem).unwrap().or_default();

                if !p.contains(&ty_id) {
                    p.push(ty_id);
                }
            }
        }
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

    pub fn ty_union(&mut self, tys: &[TyId]) -> TyId {
        let mut elems = vec![];

        for &ty_id in tys {
            if let Ty::Union(t) = &self.tys[ty_id] {
                elems.extend_from_slice(&t.elems);
            }
        }

        elems.sort();
        elems.dedup();

        assert!(!elems.is_empty());

        if elems.len() == 1 {
            elems[0]
        } else {
            self.add_ty(Ty::Union(TyUnion { elems }))
        }
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

            Ty::Union(t) => {
                let mut elems = t.elems.clone();

                for elem in &mut elems {
                    *elem = self.subst(*elem, map);
                }

                return self.ty_union(&elems);
            }
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

            // type unions are not related by subtyping.
            (Ty::Union(_), _) | (_, Ty::Union(_)) => false,

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

            (Ty::Error | Ty::Ctor(_) | Ty::Param(_) | Ty::Var(_) | Ty::Null | Ty::Union(_), _) => {
                self.builtin.any
            }
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

            (Ty::Error | Ty::Ctor(_) | Ty::Param(_) | Ty::Var(_) | Ty::Null | Ty::Union(_), _) => {
                None
            }
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

                Ty::Union(t) => {
                    write!(f, "(")?;

                    for (idx, &ty_id) in t.elems.iter().enumerate() {
                        if idx > 0 {
                            write!(f, " | ")?;
                        }

                        write!(f, "{}", self.format_ty(ty_id))?;
                    }

                    write!(f, ")")
                }
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
        self.replace_with_reprs();

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

    fn solve_ty(&mut self, ty_id: TyId) -> Result<TyId> {
        let vars = self.sema.tyck.var_occurrences[ty_id]
            .iter()
            .map(|&ty_id| self.sema.tyck.tys[ty_id].as_var().unwrap())
            .collect();
        let result = self.constrs.solve(self.sema, self.diag, vars);
        self.result = self.result.and(result);

        result.map(|()| self.repr(ty_id))
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

    fn replace_with_reprs(&mut self) {
        let mut exprs = mem::take(&mut self.sema.tyck.exprs);
        let mut ty_exprs = mem::take(&mut self.sema.tyck.ty_exprs);
        let mut def_tys = mem::take(&mut self.sema.tyck.def_tys);
        let mut call_targets = mem::take(&mut self.sema.tyck.call_targets);

        let ty_ids = exprs
            .values_mut()
            .chain(ty_exprs.values_mut())
            .chain(def_tys.values_mut())
            .chain(call_targets.values_mut().flat_map(|(recv, _)| match recv {
                Receiver::None => None,
                Receiver::Implicit(ty_id) | Receiver::Explicit(ty_id) => Some(ty_id),
            }));

        for ty_id in ty_ids {
            *ty_id = self.repr(*ty_id);
        }

        self.sema.tyck.exprs = exprs;
        self.sema.tyck.ty_exprs = ty_exprs;
        self.sema.tyck.def_tys = def_tys;
        self.sema.tyck.call_targets = call_targets;
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

    fn early_tyck_decl_semantic_ty(
        &mut self,
        _decl: &'ast ast::Decl,
        _d: &'ast ast::DeclSemanticTy,
    ) {
        unimplemented!()
    }

    fn early_tyck_decl_ty_alias(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclTyAlias) {
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

    fn early_tyck_decl_annotation(
        &mut self,
        _decl: &'ast ast::Decl,
        _d: &'ast ast::DeclAnnotation,
    ) {
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

    fn early_tyck_decl_variable(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclVariable) {
        // do nothing.
    }

    fn early_tyck_decl_state(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn early_tyck_decl_shift(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclShift) {
        // do nothing.
    }

    fn early_tyck_decl_constructor(
        &mut self,
        _decl: &'ast ast::Decl,
        _d: &'ast ast::DeclConstructor,
    ) {
        // do nothing.
    }

    fn early_tyck_decl_destructor(
        &mut self,
        _decl: &'ast ast::Decl,
        _d: &'ast ast::DeclDestructor,
    ) {
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

    fn check_elided_variable_ty(&mut self, decl_id: DeclId) -> Result {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let def = self.sema.name_res.def::<DefVariable>(def_id);

        let what = match def.kind {
            VariableKind::Global => "global variable",
            VariableKind::Local { .. } => return Ok(()),
            VariableKind::Field { .. } => "field",
            VariableKind::ConstructorVar { .. } => unreachable!(),
            VariableKind::Param { .. } => unreachable!(),
        };

        let Def { name, loc, .. } = &self.sema.name_res.defs[def_id];

        self.result = Err(());
        self.diag.emit(
            Diag::err()
                .at(loc.clone())
                .with_msg(format!("{what} `{name}` must have an explicit type"))
                .with_label(Label::primary(loc.clone()))
                .build(),
        );

        Err(())
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

    fn tyck_decl_semantic_ty(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclSemanticTy) {
        unimplemented!()
    }

    fn tyck_decl_ty_alias(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclTyAlias) {
        unimplemented!()
    }

    fn tyck_decl_struct(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
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
            None,
            None,
        );

        self.register_fn_sig::<DefAnnotation>(def_id, None, |_| &[], |def| &def.params, None);
    }

    fn tyck_decl_action(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        let def_id = self.sema.name_res.decl_defs[decl.id];

        self.tyck_params(
            def_id,
            d.params.iter().map(|param| param.ty_expr),
            |def: &DefAction| &def.params,
            None,
            None,
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

        let ty_id = match d.ty_expr {
            Some(ty_expr) => self.tyck_ty_expr(ty_expr),

            None if self.check_elided_variable_ty(decl.id).is_ok() => {
                self.fresh_var(VarProvenance::Var(def_id))
            }

            None => self.sema.tyck.builtin.error,
        };

        self.sema.tyck.def_tys.insert(def_id, ty_id);
    }

    fn tyck_decl_state(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn tyck_decl_shift(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclShift) {
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
        _ty_expr: &'ast ast::TyExpr,
        _t: &'ast ast::TyExprName,
        _ty_args: Vec<TyId>,
        _def_id: DefId,
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
        _ty_expr: &'ast ast::TyExpr,
        _t: &'ast ast::TyExprIntersection,
    ) {
        unimplemented!()
    }

    fn tyck_ty_expr_union(&mut self, ty_expr: &'ast ast::TyExpr, t: &'ast ast::TyExprUnion) {
        let elems = &[self.tyck_ty_expr(t.lhs), self.tyck_ty_expr(t.rhs)];
        let ty_id = self.sema.tyck.ty_union(elems);
        self.sema.tyck.ty_exprs.insert(ty_expr.id, ty_id);
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
        result: Option<(DefId, TyId)>,
        this_def_id: Option<DefId>,
    ) {
        if let Some((result_def_id, ret_ty_id)) = result {
            self.sema.tyck.def_tys.insert(result_def_id, ret_ty_id);
        }

        if let Some(this_def_id) = this_def_id {
            let this_ty = self.function_recv(def_id, ReplaceTyArgs::No).unwrap();
            self.sema.tyck.def_tys.insert(this_def_id, this_ty);
        }

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
        let def = self.sema.name_res.def::<DefFunction>(def_id);
        let recv = match def.kind {
            FunctionKind::Fun { of } => of,
            FunctionKind::Proc { of, .. } => of,
            FunctionKind::Constructor { of } => Some(of),
            FunctionKind::Destructor { of } => Some(of),
        };

        let result_def_id = def.result_def_id;
        let this_def_id = def.this_def_id;
        let ret = self.tyck_ret_ty_expr(ret);
        self.tyck_params(
            def_id,
            param_ty_exprs,
            |def: &DefFunction| &def.params,
            Some((result_def_id, ret)),
            this_def_id,
        );
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
            ast::ExprKind::ProcCall(e) => self.tyck_expr_proc_call(expr, e, expected),
            ast::ExprKind::ActionCall(e) => self.tyck_expr_action_call(expr, e, expected),
            ast::ExprKind::Instantiate(e) => self.tyck_expr_instantiate(expr, e, expected),
            ast::ExprKind::Name(e) => self.tyck_expr_name(expr, e, expected),
            ast::ExprKind::Prev(e) => self.tyck_expr_prev(expr, e, expected),
            ast::ExprKind::Field(e) => self.tyck_expr_field(expr, e, expected),
            ast::ExprKind::Index(e) => self.tyck_expr_index(expr, e, expected),
            ast::ExprKind::HasConcept(e) => self.tyck_expr_has_concept(expr, e, expected),
            ast::ExprKind::Cast(e) => self.tyck_expr_cast(expr, e, expected),
            ast::ExprKind::TyCompare(e) => self.tyck_expr_ty_compare(expr, e, expected),
            ast::ExprKind::Unary(e) => self.tyck_expr_unary(expr, e, expected),
            ast::ExprKind::Binary(e) => self.tyck_expr_binary(expr, e, expected),
        }

        self.sema.tyck.exprs[expr_id]
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

                    Some(ast::Variance::Covariant) => unimplemented!(),
                    Some(ast::Variance::Contravariant) => unimplemented!(),
                }
            }

            ast::TyArg::Wildcard(_) => unimplemented!(),
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

    fn make_wrong_field_base_ty_err(&self, loc: Loc, base_expr: ExprId, base_ty: TyId) -> Diag {
        let base_loc = self.sema.libsl.exprs[base_expr].loc.clone();

        Diag::err()
            .at(loc)
            .with_msg(format_args!(
                "cannot access a field of `{}`",
                self.sema.format_ty(base_ty),
            ))
            .with_label(Label::primary(base_loc).with_msg(format_args!(
                "this expression has type `{}`",
                self.sema.format_ty(base_ty),
            )))
            .build()
    }

    fn resolve_expr_name(
        &mut self,
        mut scope_id: ScopeId,
        name: &ast::Name,
    ) -> Result<ResolvedName> {
        let loc = &name.loc;
        let name = name.to_string();

        loop {
            let scope = &self.sema.name_res.scopes[scope_id];

            let kind = match scope.kind {
                ScopeKind::Automaton(_) | ScopeKind::Struct(_) => ResolvedNameKind::ImplicitField,
                _ => ResolvedNameKind::Var,
            };

            if let Some(def_id) = self
                .sema
                .name_res
                .try_resolve_local(scope_id, Ns::Var, &name)
            {
                return Ok(ResolvedName { kind, def_id });
            }

            match scope.parent {
                Some(parent_scope_id) => scope_id = parent_scope_id,

                None => {
                    self.result = Err(());
                    self.diag
                        .emit(NameRes::make_unresolved_name_error(&name, loc.clone()));

                    return Err(());
                }
            }
        }
    }

    fn check_assignable(&mut self, stmt: &'ast ast::Stmt, lhs: ExprId) {
        let assignment = &self.sema.tyck.assignments[stmt.id];

        match *assignment {
            AssignmentKind::Var(def_id) | AssignmentKind::Field { def_id, .. } => {
                let def = self.sema.name_res.def::<DefVariable>(def_id);

                if !def.mutable {
                    let loc = &self.sema.libsl.exprs[lhs].loc;
                    let var_loc = self.sema.name_res.defs[def_id].loc.clone();
                    let var_kind = if matches!(assignment, AssignmentKind::Var(_)) {
                        "variable"
                    } else {
                        "field"
                    };

                    self.result = Err(());
                    self.diag.emit(
                        Diag::err()
                            .at(loc.clone())
                            .with_msg(format!("cannot assign to immutable {var_kind}"))
                            .with_label(Label::primary(loc.clone()))
                            .with_label(
                                Label::secondary(var_loc)
                                    .with_msg(format!("{var_kind} defined here")),
                            )
                            .build(),
                    );
                }
            }

            AssignmentKind::Index => {
                // always assignable.
            }
        }
    }

    fn ty_param_map_from_args(
        &self,
        generics: &[DefId],
        args: &[TyId],
    ) -> SparseSecondaryMap<TyId, TyId> {
        generics
            .iter()
            .map(|&def_id| self.sema.tyck.def_tys[def_id])
            .zip(args.iter().copied())
            .collect()
    }

    fn function_recv(&mut self, def_id: DefId, replace_ty_args: ReplaceTyArgs) -> Option<TyId> {
        match self.sema.name_res.def::<DefFunction>(def_id).kind {
            FunctionKind::Fun { of } | FunctionKind::Proc { of, .. } => {
                of.map(|of| self.make_recv_ty(of, replace_ty_args))
            }

            FunctionKind::Constructor { of } | FunctionKind::Destructor { of } => {
                Some(self.make_recv_ty(of, replace_ty_args))
            }
        }
    }

    fn find_implicit_recv(
        &mut self,
        expr_id: ExprId,
        replace_ty_args: ReplaceTyArgs,
    ) -> Option<TyId> {
        match self.sema.name_res.exprs[expr_id].kind {
            ExprCtxKind::EnumSemanticTyValue(_) => return None,
            ExprCtxKind::AnnotationParam(_) => return None,

            ExprCtxKind::VariableInit(def_id) => {
                match self.sema.name_res.def::<DefVariable>(def_id).kind {
                    VariableKind::Global => return None,

                    VariableKind::Local { of } => self.function_recv(of, replace_ty_args),

                    VariableKind::Field { of } => Some(self.make_recv_ty(of, replace_ty_args)),

                    VariableKind::ConstructorVar { of } => {
                        Some(self.make_recv_ty(of, replace_ty_args))
                    }

                    VariableKind::Param { of, .. } => self.function_recv(of, replace_ty_args),
                }
            }

            ExprCtxKind::FunctionBody(def_id) => self.function_recv(def_id, replace_ty_args),
        }
    }

    fn make_recv_ty(&mut self, def_id: DefId, replace_ty_args: ReplaceTyArgs) -> TyId {
        let generics = match &self.sema.name_res.defs[def_id].kind {
            DefKind::Dummy => unreachable!(),
            DefKind::Import(_) => unreachable!(),
            DefKind::TyAlias(_) => unreachable!(),

            DefKind::Struct(def) => def
                .generics
                .iter()
                .map(|&def_id| self.sema.tyck.def_tys[def_id])
                .collect::<Vec<_>>(),

            DefKind::Automaton(def) => def
                .generics
                .iter()
                .map(|&def_id| self.sema.tyck.def_tys[def_id])
                .collect::<Vec<_>>(),

            DefKind::BuiltinCtor(_)
            | DefKind::SemanticTy(_)
            | DefKind::SemanticTyEnumValue { .. }
            | DefKind::Enum(_)
            | DefKind::EnumVariant { .. }
            | DefKind::Annotation(_)
            | DefKind::Action(_)
            | DefKind::Function(_)
            | DefKind::Variable(_)
            | DefKind::State(_)
            | DefKind::TyVariable(_)
            | DefKind::Pred(_) => unreachable!(),
        };

        let ty_args = match replace_ty_args {
            ReplaceTyArgs::Yes(loc) => {
                let param_map = self.make_fresh_vars_for_ty_params(&generics, loc);

                generics.into_iter().map(|ty_id| param_map[ty_id]).collect()
            }

            ReplaceTyArgs::No => generics,
        };

        self.sema.tyck.add_ctor_ty(def_id, ty_args)
    }
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_decl_fully(&mut self, decl_id: DeclId) {
        self.early_tyck_decl(decl_id);
        self.tyck_decl(decl_id);
        self.tyck_decl_body(decl_id);
    }

    fn tyck_decl_semantic_ty_body(
        &mut self,
        _decl: &'ast ast::Decl,
        _d: &'ast ast::DeclSemanticTy,
    ) {
        unimplemented!()
    }

    fn tyck_decl_ty_alias_body(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclTyAlias) {
        unimplemented!()
    }

    fn tyck_decl_struct_body(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        // TODO: annotations.
        for &decl_id in &d.decls {
            self.tyck_decl_body(decl_id);
        }
    }

    fn tyck_decl_enum_body(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclEnum) {
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

    fn tyck_decl_action_body(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclAction) {
        // TODO: annotations.
    }

    fn tyck_decl_automaton_body(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        // TODO: annotations.
        for &decl_id in iter::chain(&d.constructor_variables, &d.decls) {
            self.tyck_decl_body(decl_id);
        }
    }

    fn tyck_decl_function_body(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
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

    fn tyck_decl_state_body(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclState) {
        // do nothing.
    }

    fn tyck_decl_shift_body(&mut self, _decl: &'ast ast::Decl, _d: &'ast ast::DeclShift) {
        // TODO: resolve overloads.
    }

    fn tyck_decl_constructor_body(
        &mut self,
        _decl: &'ast ast::Decl,
        d: &'ast ast::DeclConstructor,
    ) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_decl_destructor_body(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_decl_proc_body(&mut self, _decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        // TODO: annotations.
        if let Some(body) = &d.body {
            self.tyck_function_body(body);
        }
    }

    fn tyck_function_body(&mut self, body: &'ast ast::FunctionBody) {
        let first_var_idx = self.sema.tyck.var_provenances.len();

        for contract in &body.contracts {
            self.tyck_contract(contract);
        }

        for &stmt_id in &body.stmts {
            self.tyck_stmt(stmt_id);
        }

        let vars = (first_var_idx..self.sema.tyck.var_provenances.len()).collect::<Vec<_>>();
        self.result = self
            .result
            .and(self.constrs.solve(self.sema, self.diag, vars));
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

    fn tyck_contract_assigns(&mut self, _contract: &'ast ast::ContractAssigns) {
        unimplemented!()
    }

    fn tyck_stmt(&mut self, stmt_id: StmtId) {
        let stmt = &self.sema.libsl.stmts[stmt_id];

        match &stmt.kind {
            ast::StmtKind::Dummy => unreachable!(),
            ast::StmtKind::Decl(decl_id) => self.tyck_stmt_decl(stmt, *decl_id),
            ast::StmtKind::If(s) => self.tyck_stmt_if(stmt, s),
            ast::StmtKind::Assign(s) => self.tyck_stmt_assign(stmt, s),
            ast::StmtKind::Cancel(s) => self.tyck_stmt_cancel(stmt, s),
            ast::StmtKind::Expr(expr_id) => self.tyck_stmt_expr(stmt, *expr_id),
        }
    }

    fn tyck_stmt_decl(&mut self, _stmt: &'ast ast::Stmt, decl_id: DeclId) {
        self.tyck_decl_fully(decl_id);
    }

    fn tyck_stmt_if(&mut self, _stmt: &'ast ast::Stmt, s: &'ast ast::StmtIf) {
        self.tyck_expr(s.cond, Some(self.sema.tyck.builtin.bool));

        for &stmt_id in iter::chain(&s.then_branch, &s.else_branch) {
            self.tyck_stmt(stmt_id);
        }
    }

    fn tyck_stmt_assign(&mut self, stmt: &'ast ast::Stmt, s: &'ast ast::StmtAssign) {
        let lhs = self.tyck_expr(s.lhs, None);
        self.tyck_expr(s.rhs, Some(lhs));

        let kind = match &self.sema.libsl.exprs[s.lhs].kind {
            ast::ExprKind::Name(_) => {
                let res = &self.sema.tyck.name_exprs[s.lhs];

                match res.kind {
                    ResolvedNameKind::Var => AssignmentKind::Var(res.def_id),

                    ResolvedNameKind::ImplicitField => AssignmentKind::Field {
                        implicit: true,
                        def_id: res.def_id,
                    },
                }
            }

            ast::ExprKind::Field(_) => AssignmentKind::Field {
                implicit: false,
                def_id: self.sema.tyck.field_exprs[s.lhs],
            },

            ast::ExprKind::Index(_) => AssignmentKind::Index,

            _ => unreachable!(),
        };

        self.sema.tyck.assignments.insert(stmt.id, kind);
        self.check_assignable(stmt, s.lhs);
    }

    fn tyck_stmt_cancel(&mut self, stmt: &'ast ast::Stmt, _s: &'ast ast::StmtCancel) {
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

    fn tyck_stmt_expr(&mut self, _stmt: &'ast ast::Stmt, expr_id: ExprId) {
        self.tyck_expr(expr_id, None);
    }

    fn tyck_pred(&mut self, pred_id: PredId) {
        let pred = &self.sema.libsl.preds[pred_id];

        match &pred.kind {
            ast::PredKind::Dummy => unreachable!(),
            ast::PredKind::Block(p) => self.tyck_pred_block(pred, p),
            ast::PredKind::Named(p) => self.tyck_pred_named(pred, p),
            &ast::PredKind::Decl(decl_id) => self.tyck_pred_decl(pred, decl_id),
            ast::PredKind::If(p) => self.tyck_pred_if(pred, p),
            &ast::PredKind::Expr(expr_id) => self.tyck_pred_expr(pred, expr_id),
        }
    }

    fn tyck_pred_block(&mut self, _pred: &'ast ast::Pred, p: &'ast ast::PredBlock) {
        for &pred_id in &p.preds {
            self.tyck_pred(pred_id);
        }
    }

    fn tyck_pred_named(&mut self, _pred: &'ast ast::Pred, p: &'ast ast::PredNamed) {
        self.tyck_pred(p.pred);
    }

    fn tyck_pred_decl(&mut self, _pred: &'ast ast::Pred, decl_id: DeclId) {
        self.tyck_decl_fully(decl_id);
    }

    fn tyck_pred_if(&mut self, _pred: &'ast ast::Pred, p: &'ast ast::PredIf) {
        self.tyck_expr(p.cond, Some(self.sema.tyck.builtin.bool));
        self.tyck_pred(p.then_branch);

        if let Some(else_branch) = p.else_branch {
            self.tyck_pred(else_branch);
        }
    }

    fn tyck_pred_expr(&mut self, _pred: &'ast ast::Pred, expr_id: ExprId) {
        self.tyck_expr(expr_id, Some(self.sema.tyck.builtin.bool));
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

    fn tyck_expr_proc_call(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprProcCall,
        expected: Option<TyId>,
    ) {
        self.sema
            .tyck
            .exprs
            .insert(expr.id, self.sema.tyck.builtin.error);

        let recv = e
            .recv
            .map(|expr_id| {
                let ty_id = self.tyck_expr(expr_id, None);

                self.solve_ty(ty_id)
            })
            .transpose();

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

        let Ok(recv) = recv else {
            return;
        };

        if recv == Some(self.sema.tyck.builtin.error) {
            return;
        }

        let recv = match recv {
            Some(recv) => Receiver::Implicit(recv),
            None => match self.find_implicit_recv(expr.id, ReplaceTyArgs::No) {
                Some(recv) => Receiver::Implicit(recv),
                None => Receiver::None,
            },
        };

        let Ok(def_id) = self.resolve_callee(
            &expr.loc,
            expr.id,
            &recv,
            &e.name.to_string(),
            &args,
            &ty_args,
        ) else {
            return;
        };

        self.check_ty_arg_arity(&expr.loc, ty_args.len(), self.fn_sig(def_id).generics.len());
        self.check_arg_arity(&expr.loc, args.len(), self.fn_sig(def_id).params.len());

        let sig = self.fn_sig(def_id).clone();
        let ty_param_map = self.make_fresh_vars_for_ty_params(&sig.generics, &expr.loc);

        for (&param, &arg) in iter::zip(&sig.generics, &ty_args) {
            let _ = self.constr_eq(arg, ty_param_map[param], ConstrProvenance::Expr(expr.id));
        }

        match (recv, sig.recv) {
            (Receiver::None, None) => {}

            (Receiver::Implicit(_), None) => {}

            (Receiver::Implicit(ty_id) | Receiver::Explicit(ty_id), Some(recv)) => {
                let expected = self.make_recv_ty(recv, ReplaceTyArgs::Yes(&Loc::Synthetic));
                let _ = self.constr_sub(ty_id, expected, ConstrProvenance::Expr(expr.id));
            }

            _ => unreachable!(),
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

    fn tyck_expr_name(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprName,
        expected: Option<TyId>,
    ) {
        let scope_id = self.sema.name_res.exprs[expr.id].scope_id;

        let Ok(res) = self.resolve_expr_name(scope_id, &e.name) else {
            self.sema
                .tyck
                .exprs
                .insert(expr.id, self.sema.tyck.builtin.error);

            return;
        };

        let def_id = res.def_id;
        self.sema.tyck.name_exprs.insert(expr.id, res);

        let ty_id = self.sema.tyck.def_tys[def_id];
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_prev(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprPrev,
        expected: Option<TyId>,
    ) {
        // TODO: ensure well-formedness.
        let ty_id = self.tyck_expr(e.base, expected);

        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_field(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprField,
        expected: Option<TyId>,
    ) {
        self.sema
            .tyck
            .exprs
            .insert(expr.id, self.sema.tyck.builtin.error);

        let base = self.tyck_expr(e.base, None);
        let Ok(base) = self.solve_ty(base) else {
            return;
        };

        let (scope_id, param_map) = match &self.sema.tyck.tys[base] {
            Ty::Error => return,

            Ty::Ctor(t) => match &self.sema.name_res.defs[t.ctor].kind {
                DefKind::Dummy => unreachable!(),
                DefKind::Import(_) => unreachable!(),

                DefKind::Struct(def) => (
                    self.sema.name_res.def_member_scopes[t.ctor],
                    self.ty_param_map_from_args(&def.generics, &t.args),
                ),

                DefKind::Automaton(def) => (
                    self.sema.name_res.def_member_scopes[t.ctor],
                    self.ty_param_map_from_args(&def.generics, &t.args),
                ),

                _ => {
                    self.result = Err(());
                    self.diag.emit(self.make_wrong_field_base_ty_err(
                        expr.loc.clone(),
                        e.base,
                        base,
                    ));

                    return;
                }
            },

            Ty::Var(_) => unreachable!(),

            Ty::Param(_) | Ty::Null | Ty::Union(_) => {
                self.result = Err(());
                self.diag
                    .emit(self.make_wrong_field_base_ty_err(expr.loc.clone(), e.base, base));

                return;
            }
        };

        let field = e.field.to_string();

        let Some(def_id) = self.sema.name_res.try_resolve(scope_id, Ns::Var, &field) else {
            self.result = Err(());
            self.diag.emit(
                Diag::err()
                    .at(e.field.loc.clone())
                    .with_msg(format_args!(
                        "type `{}` has no field named `{field}`",
                        self.sema.format_ty(base),
                    ))
                    .with_label(
                        Label::primary(self.sema.libsl.exprs[e.base].loc.clone()).with_msg(
                            format_args!(
                                "this expression has type `{}`",
                                self.sema.format_ty(base),
                            ),
                        ),
                    )
                    .build(),
            );

            return;
        };

        let ty_id = self.sema.tyck.def_tys[def_id];
        let ty_id = self.sema.tyck.subst(ty_id, &param_map);
        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, ty_id);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_index(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprIndex,
        expected: Option<TyId>,
    ) {
        let elem_ty = self.fresh_var(VarProvenance::Element { of: expr.id });
        let array_ty = self
            .sema
            .tyck
            .add_ctor_ty(self.sema.name_res.prelude_defs.array, vec![elem_ty]);
        self.tyck_expr(e.base, Some(array_ty));
        self.tyck_expr(e.index, Some(self.sema.tyck.builtin.int32));

        let ty_id = self.check_ty(ConstrProvenance::Expr(expr.id), expected, elem_ty);
        self.sema.tyck.exprs.insert(expr.id, ty_id);
    }

    fn tyck_expr_has_concept(
        &mut self,
        _expr: &'ast ast::Expr,
        _e: &'ast ast::ExprHasConcept,
        _expected: Option<TyId>,
    ) {
        unimplemented!()
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
