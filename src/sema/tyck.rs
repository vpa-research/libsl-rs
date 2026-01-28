//! Type checking and inference for LibSL.

use std::collections::HashMap;
use std::ops::ControlFlow;

use slotmap::{SecondaryMap, SlotMap};

use crate::diag::DiagCtx;
use crate::sema::ty::{Ty, TyId};
use crate::sema::{Result, Sema};
use crate::visit::Visitor;
use crate::{AccessId, DeclId, ExprId, LibSl, ast};

#[derive(Debug, Default)]
pub struct BuiltinTys {
    pub error: TyId,
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
        self.early_tyck_decls();
        self.tyck_decls();

        self.result
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
        todo!()
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
}

impl<'ast, D: DiagCtx> Visitor<'ast> for Pass<'ast, '_, D> {
    fn libsl(&self) -> &'ast LibSl {
        self.sema.libsl
    }

    fn visit_decl(&mut self, decl: &'ast ast::Decl) -> ControlFlow<()> {
        todo!()
    }
}
