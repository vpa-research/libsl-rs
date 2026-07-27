//! The [`Visitor`] and [`Walkable`] trait definitions.

use std::ops::ControlFlow;

use crate::AnnotationId;
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
pub trait Visitor<'ast, C = ()>
where
    C: Clone,
{
    /// Returns a refernce to [`LibSl`] to resolve entity identifiers while walking over the AST.
    fn libsl(&self) -> &'ast LibSl;

    /// Called for every walked [entity declaration][ast::Decl].
    fn visit_decl(&mut self, ctx: C, decl: &'ast ast::Decl) -> ControlFlow<()> {
        decl.walk(self, ctx)
    }

    /// Called for every walked [type expression][ast::TyExpr].
    fn visit_ty_expr(&mut self, ctx: C, ty_expr: &'ast ast::TyExpr) -> ControlFlow<()> {
        ty_expr.walk(self, ctx)
    }

    /// Called for every walked [expression][ast::Expr].
    fn visit_expr(&mut self, ctx: C, expr: &'ast ast::Expr) -> ControlFlow<()> {
        expr.walk(self, ctx)
    }

    /// Called for every walked [statement][ast::Stmt].
    fn visit_stmt(&mut self, ctx: C, stmt: &'ast ast::Stmt) -> ControlFlow<()> {
        stmt.walk(self, ctx)
    }

    /// Called for every walked [predicate expression][ast::Pred].
    fn visit_pred(&mut self, ctx: C, pred: &'ast ast::Pred) -> ControlFlow<()> {
        pred.walk(self, ctx)
    }

    /// Called for every walked [annotation use][ast::Annotation].
    fn visit_annotation(&mut self, ctx: C, annotation: &'ast ast::Annotation) -> ControlFlow<()> {
        annotation.walk(self, ctx)
    }
}

/// Allows walking the substructure recursively.
pub trait Walkable {
    /// Walks the substructure of `Self`.
    ///
    /// It **does not** call the visitor's hook method for `self`, only its descendant nodes.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone;

    /// Walks the substructure of `Self`.
    ///
    /// Unlike [`walk`], if this type has a corresponding `visit` method in the [`Visitor`],
    /// `walk_self` dispatches to it instead.
    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.walk(visitor, ctx)
    }
}

impl Walkable for ast::Decl {
    /// Walks the substructure of an [entity declaration][ast::Decl].
    ///
    /// It **does not** call [`Visitor::visit_decl`] for the provided `decl`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.kind.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_decl(ctx, self)
    }
}

impl Walkable for ast::TyExpr {
    /// Walks the substructure of a [type expression][ast::TyExpr].
    ///
    /// It **does not** call [`Visitor::visit_ty_expr`] for the provided `ty_expr`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.kind.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_ty_expr(ctx, self)
    }
}

impl Walkable for ast::Expr {
    /// Walks the substructure of an [expression][ast::Expr].
    ///
    /// It **does not** call [`Visitor::visit_expr`] for the provided `expr`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.kind.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_expr(ctx, self)
    }
}

impl Walkable for ast::Stmt {
    /// Walks the substructure of a [statement][ast::Stmt].
    ///
    /// It **does not** call [`Visitor::visit_stmt`] for the provided `stmt`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.kind.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_stmt(ctx, self)
    }
}

impl Walkable for ast::Pred {
    /// Walks the substructure of a [predicate expression][ast::Pred].
    ///
    /// It **does not** call [`Visitor::visit_pred`] for the provided `pred`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.kind.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_pred(ctx, self)
    }
}

impl Walkable for ast::Annotation {
    /// Walks the substructure of an [annotation use][ast::Annotation].
    ///
    /// It **does not** call [`Visitor::visit_annotation`] for the provided `annotation`.
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        self.args.walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.visit_annotation(ctx, self)
    }
}

impl Walkable for DeclId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().decls[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().decls[*self].walk_self(visitor, ctx)
    }
}

impl Walkable for TyExprId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().ty_exprs[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().ty_exprs[*self].walk_self(visitor, ctx)
    }
}

impl Walkable for ExprId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().exprs[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().exprs[*self].walk_self(visitor, ctx)
    }
}

impl Walkable for StmtId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().stmts[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().stmts[*self].walk_self(visitor, ctx)
    }
}

impl Walkable for PredId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().preds[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().preds[*self].walk_self(visitor, ctx)
    }
}

impl Walkable for AnnotationId {
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().annotations[*self].walk(visitor, ctx)
    }

    fn walk_self<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        visitor.libsl().annotations[*self].walk_self(visitor, ctx)
    }
}

impl<T> Walkable for [T]
where
    T: Walkable,
{
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        for elem in self {
            elem.walk_self(visitor, ctx.clone())?;
        }

        ControlFlow::Continue(())
    }
}

impl<T> Walkable for Vec<T>
where
    T: Walkable,
{
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        <[T]>::walk_self(self, visitor, ctx)
    }
}

impl<T> Walkable for Option<T>
where
    T: Walkable,
{
    fn walk<'ast, V, C>(&'ast self, visitor: &mut V, ctx: C) -> ControlFlow<()>
    where
        V: Visitor<'ast, C> + ?Sized,
        C: Clone,
    {
        match self {
            Some(elem) => elem.walk_self(visitor, ctx),
            None => ControlFlow::Continue(()),
        }
    }
}
