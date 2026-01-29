//! Type checking and inference for LibSL.

use std::collections::HashMap;
use std::ops::ControlFlow;

use slotmap::{SecondaryMap, SlotMap};

use crate::diag::DiagCtx;
use crate::sema::def::{DefId, DefKind};
use crate::sema::ty::{BuiltinTyCtor, ConstructedTy, FloatCtor, IntCtor, IntWidth, Ty, TyId};
use crate::sema::tyck::constraints::{BoundSet, ConstrSet};
use crate::sema::{Result, Sema};
use crate::visit::Visitor;
use crate::{AccessId, DeclId, ExprId, LibSl, TyExprId, ast};

mod constraints;

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

#[derive(Debug, Default)]
pub struct TyCk {
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: HashMap<Ty, TyId>,
    pub builtin: BuiltinTys,
    pub exprs: SecondaryMap<ExprId, TyId>,
    pub accesses: SecondaryMap<AccessId, TyId>,
    pub ty_exprs: SecondaryMap<TyExprId, TyId>,

    constrs: ConstrSet,
    bounds: BoundSet,
}

impl TyCk {
    pub fn add_ty(&mut self, ty: Ty) -> TyId {
        *self
            .ty_dedup
            .entry(ty)
            .or_insert_with_key(|ty| self.tys.insert(ty.clone()))
    }
}

impl Sema<'_> {
    /// Performs type checking and inference.
    pub fn tyck(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

struct Pass<'ast, 's, D> {
    sema: &'s mut Sema<'ast>,
    diag: &'s mut D,
    result: Result,
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn new(sema: &'s mut Sema<'ast>, diag: &'s mut D) -> Self {
        Self {
            sema,
            diag,
            result: Ok(()),
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

            *prelude(&mut self.sema.tyck.builtin) = ty_id;
        }

        self.sema.tyck.builtin.error = self.sema.tyck.add_ty(Ty::Error);
        self.sema.tyck.builtin.null = self.sema.tyck.add_ty(Ty::Null);
    }

    fn lit_ty(&self, lit: &ast::PrimitiveLit) -> TyId {
        // FIXME: this method should return a literal type instead of widening it.
        let builtin = &self.sema.tyck.builtin;

        match lit {
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
        }
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
        // TODO: tyck annotations.

        self.tyck_ty_expr(d.real_ty);

        match &d.kind {
            ast::SemanticTyKind::Simple => {}

            ast::SemanticTyKind::Enumerated(values) => {
                for value in values {
                    todo!()
                }
            }
        }
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
                self.visit_decl(&self.sema.libsl.decls[decl_id]);
            }
        }
    }

    fn tyck_ty_expr(&mut self, ty_expr_id: TyExprId) -> TyId {
        let ty_expr = &self.sema.libsl.ty_exprs[ty_expr_id];
        self.visit_ty_expr(ty_expr);

        self.sema.tyck.ty_exprs[ty_expr_id]
    }

    fn tyck_expr(&mut self, expr_id: ExprId) -> TyId {
        let expr = &self.sema.libsl.exprs[expr_id];
        self.visit_expr(expr);

        self.sema.tyck.exprs[expr_id]
    }

    fn tyck_access(&mut self, access_id: AccessId) -> TyId {
        let access = &self.sema.libsl.accesses[access_id];
        self.visit_access(access);

        self.sema.tyck.accesses[access_id]
    }
}

impl<'ast, D: DiagCtx> Visitor<'ast> for Pass<'ast, '_, D> {
    fn libsl(&self) -> &'ast LibSl {
        self.sema.libsl
    }

    fn visit_decl(&mut self, decl: &'ast ast::Decl) -> ControlFlow<()> {
        todo!()
    }
}
