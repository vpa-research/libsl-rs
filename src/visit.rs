//! The [`Visitor`] and [`Walkable`] trait definitions.

use std::ops::ControlFlow;

use crate::AccessId;
use crate::DeclId;
use crate::ExprId;
use crate::LibSl;
use crate::PredId;
use crate::StmtId;
use crate::TyExprId;
use crate::ast;

/// Provides hooks called while walking an AST.
///
/// Default implementations call the `walk` method to descend recursively.
#[allow(unused_variables)]
pub trait Visitor<'ast> {
    /// Returns a refernce to [`LibSl`] to resolve entity identifiers while walking over the AST.
    fn libsl(&self) -> &'ast LibSl;

    /// Called for every walked [entity declaration][ast::Decl].
    fn visit_decl(&mut self, decl: &'ast ast::Decl) -> ControlFlow<()> {
        decl.walk(self)
    }

    /// Called for every walked [type expression][ast::TyExpr].
    fn visit_ty_expr(&mut self, ty_expr: &'ast ast::TyExpr) -> ControlFlow<()> {
        ty_expr.walk(self)
    }

    /// Called for every walked [expression][ast::Expr].
    fn visit_expr(&mut self, expr: &'ast ast::Expr) -> ControlFlow<()> {
        expr.walk(self)
    }

    /// Called for every walked [statement][ast::Stmt].
    fn visit_stmt(&mut self, stmt: &'ast ast::Stmt) -> ControlFlow<()> {
        stmt.walk(self)
    }

    /// Called for every walked [access expression][ast::Access].
    fn visit_access(&mut self, access: &'ast ast::Access) -> ControlFlow<()> {
        access.walk(self)
    }

    /// Called for every walked [predicate expression][ast::Pred].
    fn visit_pred(&mut self, pred: &'ast ast::Pred) -> ControlFlow<()> {
        pred.walk(self)
    }
}

/// Allows walking the substructure recursively.
pub trait Walkable {
    /// Walks the substructure of `Self`.
    ///
    /// It **does not** call the visitor's hook method for `self`, only its descendant nodes.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()>;
}

impl Walkable for ast::Decl {
    /// Walks the substructure of an [entity declaration][ast::Decl].
    ///
    /// It **does not** call [`Visitor::visit_decl`] for the provided `decl`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for ast::TyExpr {
    /// Walks the substructure of a [type expression][ast::TyExpr].
    ///
    /// It **does not** call [`Visitor::visit_ty_expr`] for the provided `ty_expr`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for ast::Expr {
    /// Walks the substructure of an [expression][ast::Expr].
    ///
    /// It **does not** call [`Visitor::visit_expr`] for the provided `expr`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for ast::Stmt {
    /// Walks the substructure of a [statement][ast::Stmt].
    ///
    /// It **does not** call [`Visitor::visit_stmt`] for the provided `stmt`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for ast::Access {
    /// Walks the substructure of an [access expression][ast::Access].
    ///
    /// It **does not** call [`Visitor::visit_access`] for the provided `access`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for ast::Pred {
    /// Walks the substructure of a [predicate expression][ast::Pred].
    ///
    /// It **does not** call [`Visitor::visit_pred`] for the provided `pred`.
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        self.kind.walk(visitor)
    }
}

impl Walkable for DeclId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().decls[*self].walk(visitor)
    }
}

impl Walkable for TyExprId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().ty_exprs[*self].walk(visitor)
    }
}

impl Walkable for ExprId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().exprs[*self].walk(visitor)
    }
}

impl Walkable for StmtId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().stmts[*self].walk(visitor)
    }
}

impl Walkable for AccessId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().accesses[*self].walk(visitor)
    }
}

impl Walkable for PredId {
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        visitor.libsl().preds[*self].walk(visitor)
    }
}

impl<T> Walkable for [T]
where
    T: Walkable,
{
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        for elem in self {
            elem.walk(visitor)?;
        }

        ControlFlow::Continue(())
    }
}

impl<T> Walkable for Vec<T>
where
    T: Walkable,
{
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        <[T]>::walk(self, visitor)
    }
}

impl<T> Walkable for Option<T>
where
    T: Walkable,
{
    fn walk<'ast, V: Visitor<'ast> + ?Sized>(&'ast self, visitor: &mut V) -> ControlFlow<()> {
        match self {
            Some(elem) => elem.walk(visitor),
            None => ControlFlow::Continue(()),
        }
    }
}
