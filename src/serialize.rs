//! Implements [`Serialize`][serde::Serialize] for the AST.

use serde::Serialize;
use serde::ser::{SerializeSeq, SerializeStruct};

use crate::loc::{Loc, Span};
use crate::{DeclId, ExprId, LibSlNode, QualifiedAccessId, StmtId, TyExprId, WithLibSl, ast};

impl<'a, T> Serialize for LibSlNode<'a, [T]>
where
    LibSlNode<'a, T>: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.inner().len()))?;

        for element in self.inner() {
            seq.serialize_element(&LibSlNode::new(element, self.libsl()))?;
        }

        seq.end()
    }
}

impl<'a, T> Serialize for LibSlNode<'a, Vec<T>>
where
    LibSlNode<'a, T>: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|vec| vec.as_slice()).serialize(serializer)
    }
}

impl<'a, T> Serialize for LibSlNode<'a, Option<T>>
where
    LibSlNode<'a, T>: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.transpose().serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, DeclId> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|&decl_id| &self.libsl().decls[decl_id])
            .serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, TyExprId> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|&ty_expr_id| &self.libsl().ty_exprs[ty_expr_id])
            .serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, ExprId> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|&expr_id| &self.libsl().exprs[expr_id])
            .serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, StmtId> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|&stmt_id| &self.libsl().stmts[stmt_id])
            .serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, QualifiedAccessId> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.map(|&qid| &self.libsl().qualified_accesses[qid])
            .serialize(serializer)
    }
}

impl Serialize for LibSlNode<'_, Span> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Span", 5)?;
        state.serialize_field("start", &self.inner().start)?;
        state.serialize_field("len", &self.inner().len)?;
        state.serialize_field("file", &self.libsl().filename_by_id(self.inner().file_id))?;
        state.serialize_field("line", &self.inner().line)?;
        state.serialize_field("col", &self.inner().col)?;

        state.end()
    }
}

impl Serialize for LibSlNode<'_, Loc> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        Ok(match self.inner() {
            Loc::Synthetic => serializer.serialize_unit_struct("Synthetic")?,
            Loc::Span(span) => span.with_libsl(self.libsl()).serialize(serializer)?,
        })
    }
}

impl Serialize for LibSlNode<'_, ast::Decl> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Decl", 2)?;
        state.serialize_field("loc", &self.map(|decl| &decl.loc))?;
        state.serialize_field("kind", &self.map(|decl| &decl.kind))?;

        state.end()
    }
}

impl Serialize for LibSlNode<'_, ast::Stmt> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Stmt", 2)?;
        state.serialize_field("loc", &self.map(|decl| &decl.loc))?;
        state.serialize_field("kind", &self.map(|decl| &decl.kind))?;

        state.end()
    }
}

impl Serialize for LibSlNode<'_, ast::TyExpr> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("TyExpr", 2)?;
        state.serialize_field("loc", &self.map(|decl| &decl.loc))?;
        state.serialize_field("kind", &self.map(|decl| &decl.kind))?;

        state.end()
    }
}

impl Serialize for LibSlNode<'_, ast::Expr> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Expr", 2)?;
        state.serialize_field("loc", &self.map(|decl| &decl.loc))?;
        state.serialize_field("kind", &self.map(|decl| &decl.kind))?;

        state.end()
    }
}

impl Serialize for LibSlNode<'_, ast::QualifiedAccess> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("QualifiedAccess", 2)?;
        state.serialize_field("loc", &self.map(|decl| &decl.loc))?;
        state.serialize_field("kind", &self.map(|decl| &decl.kind))?;

        state.end()
    }
}
