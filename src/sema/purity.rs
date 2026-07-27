//! Purity analysis.

use std::ops::ControlFlow;

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{DefFunction, FunctionKind};
use crate::sema::def::{DefVariable, VariableKind};
use crate::sema::tyck::ResolvedNameKind;
use crate::sema::{Result, Sema};
use crate::visit::{Visitor, Walkable};
use crate::{LibSl, ast};

use super::SemaError;

#[derive(Debug, Clone, Copy)]
enum AccessMode {
    Read,
    Write,
}

impl Sema<'_> {
    /// Checks all `pure` procedures to ensure they only contain allowed operations.
    pub fn check_pure(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

fn make_err(loc: Loc, op_name: &str) -> Diag {
    Diag::err()
        .at(loc.clone())
        .with_msg(format_args!(
            "{op_name} are not allowed in a pure procedure"
        ))
        .with_label(Label::primary(loc))
        .build()
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
        for file in self.sema.libsl.files.values() {
            for &decl_id in &file.decls {
                let _ = self.visit_decl((), &self.sema.libsl.decls[decl_id]);
            }
        }

        self.result
    }

    fn record_err(&mut self, diag: Diag) {
        self.result = Err(SemaError);
        self.diag.emit(diag);
    }
}

impl<'ast, D> Visitor<'ast> for Pass<'ast, '_, D>
where
    D: DiagCtx,
{
    fn libsl(&self) -> &'ast LibSl {
        self.sema.libsl
    }

    fn visit_decl(&mut self, _: (), decl: &'ast ast::Decl) -> ControlFlow<()> {
        match &decl.kind {
            ast::DeclKind::Proc(decl) if decl.is_pure => {
                let mut checker = ProcChecker { pass: self };
                decl.walk(&mut checker, AccessMode::Read)?;

                ControlFlow::Continue(())
            }

            ast::DeclKind::Struct(_) | ast::DeclKind::Automaton(_) => decl.walk(self, ()),

            ast::DeclKind::Dummy
            | ast::DeclKind::Import(_)
            | ast::DeclKind::Include(_)
            | ast::DeclKind::SemanticTy(_)
            | ast::DeclKind::TyAlias(_)
            | ast::DeclKind::Enum(_)
            | ast::DeclKind::Annotation(_)
            | ast::DeclKind::Action(_)
            | ast::DeclKind::Function(_)
            | ast::DeclKind::Proc(_)
            | ast::DeclKind::Variable(_)
            | ast::DeclKind::State(_)
            | ast::DeclKind::Shift(_)
            | ast::DeclKind::Constructor(_)
            | ast::DeclKind::Destructor(_) => ControlFlow::Continue(()),
        }
    }
}

struct ProcChecker<'ast, 'diag, 'ctx, D> {
    pass: &'ctx mut Pass<'ast, 'diag, D>,
}

impl<'ast, D: DiagCtx> ProcChecker<'ast, '_, '_, D> {
    fn check_proc_call(&mut self, expr: &'ast ast::Expr) {
        let (_, call_target) = self.pass.sema.tyck.call_targets[expr.id];

        if let FunctionKind::Proc { pure: true, .. } =
            self.pass.sema.name_res.def::<DefFunction>(call_target).kind
        {
            return;
        }

        self.pass
            .record_err(make_err(expr.loc.clone(), "calls to non-pure procedures"));
    }

    fn check_expr_name(&mut self, expr: &'ast ast::Expr, mode: AccessMode) {
        let res = &self.pass.sema.tyck.name_exprs[expr.id];

        match res.kind {
            ResolvedNameKind::Var => {
                let what = match self.pass.sema.name_res.def::<DefVariable>(res.def_id).kind {
                    VariableKind::Global => "global variables",

                    // local variables and parameters can be used freely.
                    VariableKind::Local { .. } | VariableKind::Param { .. } => return,

                    VariableKind::Field { .. } | VariableKind::ConstructorVar { .. } => "fields",

                    VariableKind::EnumVariant { .. } => return,
                };

                let msg = match mode {
                    AccessMode::Read => format!("reads of {what}"),
                    AccessMode::Write => format!("writes to {what}"),
                };
                self.pass.record_err(make_err(expr.loc.clone(), &msg));
            }

            ResolvedNameKind::ImplicitField => {
                // same as `this.$name`, which is allowed.
            }

            ResolvedNameKind::MemberScope(_) => {}
        }
    }
}

impl<'ast, D: DiagCtx> Visitor<'ast, AccessMode> for ProcChecker<'ast, '_, '_, D> {
    fn libsl(&self) -> &'ast LibSl {
        self.pass.libsl()
    }

    fn visit_stmt(&mut self, _: AccessMode, stmt: &'ast ast::Stmt) -> ControlFlow<()> {
        match &stmt.kind {
            ast::StmtKind::Dummy => panic!("encountered a dummy stmt"),
            ast::StmtKind::Decl(_) => {}
            ast::StmtKind::If(_) => {}

            ast::StmtKind::Assign(s) => {
                s.lhs.walk(self, AccessMode::Write)?;
                s.rhs.walk(self, AccessMode::Read)?;

                return ControlFlow::Continue(());
            }

            ast::StmtKind::Cancel(_) => {}
            ast::StmtKind::Expr(_) => {}
        }

        stmt.walk(self, AccessMode::Read)
    }

    fn visit_expr(&mut self, ctx: AccessMode, expr: &'ast ast::Expr) -> ControlFlow<()> {
        match &expr.kind {
            ast::ExprKind::Dummy => panic!("encountered a dummy expr"),
            ast::ExprKind::PrimitiveLit(_) => {}
            ast::ExprKind::ArrayLit(_) => {}
            ast::ExprKind::SetLit(_) => {}

            ast::ExprKind::Prev(_) => {
                self.pass
                    .record_err(make_err(expr.loc.clone(), "previous-value expressions"));
            }

            ast::ExprKind::ProcCall(_) => {
                self.check_proc_call(expr);
            }

            ast::ExprKind::ActionCall(_) => {
                self.pass
                    .record_err(make_err(expr.loc.clone(), "action calls"));
            }

            ast::ExprKind::Instantiate(_) => {
                self.pass
                    .record_err(make_err(expr.loc.clone(), "automaton instantiations"));
            }

            ast::ExprKind::HasConcept(_) => {}
            ast::ExprKind::Cast(_) => {}
            ast::ExprKind::TyCompare(_) => {}
            ast::ExprKind::Unary(_) => {}
            ast::ExprKind::Binary(_) => {}

            ast::ExprKind::Name(_) => {
                self.check_expr_name(expr, ctx);
            }

            ast::ExprKind::Field(e) => {
                e.base.walk(self, ctx)?;

                return ControlFlow::Continue(());
            }

            ast::ExprKind::Deref(_) => {
                self.pass.record_err(make_err(
                    expr.loc.clone(),
                    "pointer dereference expressions",
                ));
            }

            ast::ExprKind::Index(e) => {
                e.base.walk(self, ctx)?;
                e.index.walk(self, AccessMode::Read)?;

                return ControlFlow::Continue(());
            }
        }

        expr.walk(self, AccessMode::Read)
    }
}
