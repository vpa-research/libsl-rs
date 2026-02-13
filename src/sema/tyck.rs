//! Type checking and inference for LibSL.

use std::collections::HashMap;
use std::fmt::{self, Display};

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap};

use crate::ast::Variance;
use crate::diag::DiagCtx;
use crate::loc::Loc;
use crate::sema::def::DefId;
use crate::sema::ty::{BuiltinTyCtor, ConstructedTy, FloatCtor, IntCtor, IntWidth, Ty, TyId};
use crate::sema::tyck::constraints::{ConstrSet, VarProvenance};
use crate::sema::{Result, Sema};
use crate::{AccessId, DeclId, ExprId, TyExprId, ast};

mod constraints;
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

#[derive(Debug)]
pub struct FnTyInfo {
    pub recv: Option<DefId>,
    pub generics: Vec<DefId>,
    pub params: Vec<TyId>,
    pub ret: TyId,
}

#[derive(Debug, Default)]
pub struct TyCk {
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: HashMap<Ty, TyId>,
    pub builtin: BuiltinTys,
    pub exprs: SecondaryMap<ExprId, TyId>,
    pub accesses: SecondaryMap<AccessId, TyId>,
    pub ty_exprs: SecondaryMap<TyExprId, TyId>,
    pub def_tys: SecondaryMap<DefId, TyId>,
    pub fns: SparseSecondaryMap<DefId, FnTyInfo>,
    pub ctor_variances: SparseSecondaryMap<DefId, Vec<Variance>>,

    var_occurrences: SecondaryMap<TyId, Vec<TyId>>,
    var_provenances: Vec<VarProvenance>,
}

impl TyCk {
    pub fn add_ty(&mut self, ty: Ty) -> TyId {
        *self.ty_dedup.entry(ty).or_insert_with_key(|ty| {
            let ty_id = self.tys.insert(ty.clone());
            let mut occurrences = vec![];

            // TODO: yank this out into a method.
            match ty {
                Ty::Error => {}

                Ty::Ctor(t) => {
                    for &arg in &t.args {
                        occurrences.extend(&self.var_occurrences[arg])
                    }
                }

                Ty::Var(_) => {}

                Ty::Null => {}
            }

            self.var_occurrences.insert(ty_id, occurrences);

            ty_id
        })
    }

    pub fn add_ctor_ty(&mut self, ctor: DefId, args: Vec<TyId>) -> TyId {
        self.add_ty(Ty::Ctor(ConstructedTy { ctor, args }))
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
    pub fn format_signature(&self, def_id: DefId) -> impl Display {
        let info = &self.tyck.fns[def_id];

        fmt::from_fn(move |f| {
            // TODO: receiver.

            write!(f, "{}", self.name_res.defs[def_id].name)?;

            if !info.generics.is_empty() {
                write!(f, "<")?;

                for (idx, &generic) in info.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", self.name_res.defs[generic].name)?;
                }

                write!(f, ">")?;
            }

            write!(f, "(")?;

            for (idx, &param_ty_id) in info.params.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.format_ty(param_ty_id))?;
            }

            write!(f, "): {}", self.format_ty(info.ret))?;

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
            self.sema.tyck.ctor_variances.insert(def_id, ctor.variance().into());

            *prelude(&mut self.sema.tyck.builtin) = ty_id;
        }

        self.sema.tyck.builtin.error = self.sema.tyck.add_ty(Ty::Error);
        self.sema.tyck.builtin.null = self.sema.tyck.add_ty(Ty::Null);

        let ctors = &[
            (self.sema.name_res.prelude_defs.array, BuiltinTyCtor::Array),
            (self.sema.name_res.prelude_defs.set, BuiltinTyCtor::Set),
        ];

        for (def_id, ctor) in ctors {
            self.sema.name_res.defs[def_id].kind = ctor.clone().into();
            self.sema.tyck.ctor_variances.insert(def_id, ctor.variance().into());
        }
    }

    fn lit_ty(&mut self, loc: &Loc, lit: &ast::PrimitiveLit, expected: Option<TyId>) -> TyId {
        // FIXME: check if we expect a literal type and return that if so.
        let builtin = &self.sema.tyck.builtin;

        let ty_id = match lit {
            ast::PrimitiveLit::Int(lit) => match lit {
                ast::IntLit::I8(_) => builtin.int8,
                ast::IntLit::U8(_) => builtin.unsigned8,
                ast::IntLit::I16(_) => builtin.int16,
                ast::IntLit::U16(_) => builtin.unsigned16,
                ast::IntLit::I32(_) => builtin.int32,
                ast::IntLit::U32(_) => builtin.unsigned32,
                ast::IntLit::I64(_) => builtin.int64,
                ast::IntLit::U64(_) => builtin.unsigned64,
            },

            ast::PrimitiveLit::Float(lit) => match lit {
                ast::FloatLit::F32(_) => builtin.float32,
                ast::FloatLit::F64(_) => builtin.float64,
            },

            ast::PrimitiveLit::String(_) => builtin.string,
            ast::PrimitiveLit::Char(_) => builtin.char,
            ast::PrimitiveLit::Bool(_) => builtin.bool,
            ast::PrimitiveLit::Null => builtin.null,
        };

        self.check_ty(loc, expected, ty_id)
    }
}

// The early type-checking phase: initialize signatures of globally visible entities.
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
        // do nothing.
    }

    fn early_tyck_decl_ty_alias(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclTyAlias) {
        todo!()
    }

    fn early_tyck_decl_struct(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        todo!()
    }

    fn early_tyck_decl_enum(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclEnum) {
        todo!()
    }

    fn early_tyck_decl_annotation(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAnnotation) {
        todo!()
    }

    fn early_tyck_decl_action(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        todo!()
    }

    fn early_tyck_decl_automaton(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        todo!()
    }

    fn early_tyck_decl_function(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
        todo!()
    }

    fn early_tyck_decl_variable(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclVariable) {
        todo!()
    }

    fn early_tyck_decl_state(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclState) {
        todo!()
    }

    fn early_tyck_decl_shift(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclShift) {
        todo!()
    }

    fn early_tyck_decl_constructor(
        &mut self,
        decl: &'ast ast::Decl,
        d: &'ast ast::DeclConstructor,
    ) {
        todo!()
    }

    fn early_tyck_decl_destructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        todo!()
    }

    fn early_tyck_decl_proc(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        todo!()
    }
}

// The main type-checking phase.
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

    fn tyck_ty_expr(&mut self, ty_expr_id: TyExprId) -> TyId {
        let ty_expr = &self.sema.libsl.ty_exprs[ty_expr_id];
        todo!();

        self.sema.tyck.ty_exprs[ty_expr_id]
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

    fn check_ty(&mut self, loc: &Loc, expected: Option<TyId>, actual: TyId) -> TyId {
        todo!()
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
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_decl_semantic_ty(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclSemanticTy) {
        todo!()
    }

    fn tyck_decl_ty_alias(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclTyAlias) {
        todo!()
    }

    fn tyck_decl_struct(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclStruct) {
        todo!()
    }

    fn tyck_decl_enum(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclEnum) {
        todo!()
    }

    fn tyck_decl_annotation(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAnnotation) {
        todo!()
    }

    fn tyck_decl_action(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAction) {
        todo!()
    }

    fn tyck_decl_automaton(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclAutomaton) {
        todo!()
    }

    fn tyck_decl_function(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclFunction) {
        todo!()
    }

    fn tyck_decl_variable(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclVariable) {
        todo!()
    }

    fn tyck_decl_state(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclState) {
        todo!()
    }

    fn tyck_decl_shift(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclShift) {
        todo!()
    }

    fn tyck_decl_constructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclConstructor) {
        todo!()
    }

    fn tyck_decl_destructor(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclDestructor) {
        todo!()
    }

    fn tyck_decl_proc(&mut self, decl: &'ast ast::Decl, d: &'ast ast::DeclProc) {
        todo!()
    }
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn tyck_expr_primitive_lit(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprPrimitiveLit,
        expected: Option<TyId>,
    ) {
        let ty_id = self.lit_ty(&expr.loc, &e.lit, expected);

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

        let ty_id = self.sema.tyck.add_ctor_ty(
            self.sema.name_res.prelude_defs.array,
            vec![elem_ty_id.into()],
        );
        let ty_id = self.check_ty(&expr.loc, expected, ty_id);

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
            .add_ctor_ty(self.sema.name_res.prelude_defs.set, vec![elem_ty_id.into()]);
        let ty_id = self.check_ty(&expr.loc, expected, ty_id);

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
        let args = e
            .args
            .iter()
            .copied()
            .map(|arg| self.tyck_expr(arg, None))
            .collect::<Vec<_>>();

        let ty_args = e
            .generics
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|ty_arg| self.tyck_ty_arg(ty_arg))
            .collect::<Vec<_>>();

        if let Ok(def_id) = self.resolve_callee(e.callee, &args, &ty_args) {
            todo!()
        }

        todo!()
    }

    fn tyck_expr_action_call(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprActionCall,
        expected: Option<TyId>,
    ) {
        todo!()
    }

    fn tyck_expr_instantiate(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprInstantiate,
        expected: Option<TyId>,
    ) {
        todo!()
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
        todo!()
    }

    fn tyck_expr_ty_compare(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprTyCompare,
        expected: Option<TyId>,
    ) {
        todo!()
    }

    fn tyck_expr_unary(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprUnary,
        expected: Option<TyId>,
    ) {
        todo!()
    }

    fn tyck_expr_binary(
        &mut self,
        expr: &'ast ast::Expr,
        e: &'ast ast::ExprBinary,
        expected: Option<TyId>,
    ) {
        todo!()
    }
}
