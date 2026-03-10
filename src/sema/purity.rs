//! Purity analysis.

use std::ops::ControlFlow;

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::visit::{Visitor, Walkable};
use crate::{LibSl, ast};

/// Checks all `pure` procedures to ensure they only contain allowed operations.
///
/// Returns `true` if no violations are found.
pub fn check_pure(diag: &mut impl DiagCtx, libsl: &LibSl, file: &ast::File) -> bool {
    let mut checker = PureProcFinder {
        diag,
        libsl,
        ok: true,
    };

    for &decl_id in &file.decls {
        let cf = checker.visit_decl(&libsl.decls[decl_id]);
        debug_assert!(cf.is_continue());
    }

    checker.ok
}

fn make_err(loc: Loc, op_name: &str) -> Diag {
    Diag::err()
        .at(loc.clone())
        .with_msg(format_args!("{op_name} cannot be used in a pure procedure"))
        .with_label(Label::primary(loc))
        .build()
}

struct PureProcFinder<'ast, 'diag, D> {
    diag: &'diag mut D,
    libsl: &'ast LibSl,
    ok: bool,
}

impl<'ast, D> PureProcFinder<'ast, '_, D>
where
    D: DiagCtx,
{
    fn record_err(&mut self, diag: Diag) {
        self.diag.emit(diag);
        self.ok = false;
    }
}

impl<'ast, D> Visitor<'ast> for PureProcFinder<'ast, '_, D>
where
    D: DiagCtx,
{
    fn libsl(&self) -> &'ast LibSl {
        self.libsl
    }

    fn visit_decl(&mut self, decl: &'ast ast::Decl) -> ControlFlow<()> {
        match &decl.kind {
            ast::DeclKind::Proc(decl) if decl.is_pure => {
                let mut checker = Checker { ctx: self };
                decl.walk(&mut checker)?;

                ControlFlow::Continue(())
            }

            ast::DeclKind::Struct(_) | ast::DeclKind::Automaton(_) => decl.walk(self),

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

struct Checker<'ast, 'diag, 'ctx, D> {
    ctx: &'ctx mut PureProcFinder<'ast, 'diag, D>,
}

impl<'ast, D> Visitor<'ast> for Checker<'ast, '_, '_, D>
where
    D: DiagCtx,
{
    fn libsl(&self) -> &'ast LibSl {
        self.ctx.libsl
    }

    fn visit_stmt(&mut self, stmt: &'ast ast::Stmt) -> ControlFlow<()> {
        match &stmt.kind {
            ast::StmtKind::Dummy => panic!("encountered a dummy stmt"),
            ast::StmtKind::Decl(_) => {}
            ast::StmtKind::If(_) => {}

            // TODO: allow assignment to locals (requires name resolution).
            ast::StmtKind::Assign(_) => {
                self.ctx
                    .record_err(make_err(stmt.loc.clone(), "an assignment statement"));
            }

            ast::StmtKind::Cancel(_) => {}

            ast::StmtKind::Expr(expr_id) => expr_id.walk(self)?,
        }

        stmt.walk(self)
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr) -> ControlFlow<()> {
        match &expr.kind {
            ast::ExprKind::Dummy => panic!("encountered a dummy expr"),
            ast::ExprKind::PrimitiveLit(_) => {}
            ast::ExprKind::ArrayLit(_) => {}
            ast::ExprKind::SetLit(_) => {}
            ast::ExprKind::Prev(_) => {
                self.ctx
                    .record_err(make_err(expr.loc.clone(), "a previous-value expression"));
            }
            ast::ExprKind::ProcCall(_) => {
                // TODO: allow calls to pure procedures (requires name resolution).
                self.ctx
                    .record_err(make_err(expr.loc.clone(), "a procedure call"));
            }
            ast::ExprKind::ActionCall(_) => {
                self.ctx
                    .record_err(make_err(expr.loc.clone(), "an action call"));
            }
            ast::ExprKind::Instantiate(_) => {
                self.ctx
                    .record_err(make_err(expr.loc.clone(), "an automaton instantiation"));
            }
            ast::ExprKind::HasConcept(_) => {}
            ast::ExprKind::Cast(_) => {}
            ast::ExprKind::TyCompare(_) => {}
            ast::ExprKind::Unary(_) => {}
            ast::ExprKind::Binary(_) => {}

            ast::ExprKind::Name(_) => todo!(),
            ast::ExprKind::Field(_) => todo!(),
            ast::ExprKind::Index(_) => todo!(),
        }

        expr.walk(self)
    }
}
