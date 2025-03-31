//! A LibSL parser crate for Rust.
//!
//! To parse a LibSL source file, create a [`LibSl`] struct and call its [`LibSl::parse_file`]
//! method:
//!
//! ```
//! # use libsl::LibSl;
//! #
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let file_name = "test.libsl".into();
//! # let contents = r#"libsl "1.0.0"; library test;
//! # val x: I32 = 42;
//! # "#;
//! let mut libsl = LibSl::new();
//! let file = libsl.parse_file(file_name, contents)?;
//! # Ok(())
//! # }
//! ```
//!
//! If the file contains no syntax errors, you'll get an [`ast::File`], which is the top-level AST
//! node for a file.
//!
//! The returned AST does not store child nodes directly and instead uses identifiers (such as
//! [`ExprId`]) to refer to them. To retrieve the actual AST node, use the corresponding slotmap in
//! the [`LibSl`] struct:
//!
//! ```
//! # use libsl::LibSl;
//! #
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let file_name = "test.libsl".into();
//! # let contents = r#"libsl "1.0.0"; library test;
//! # val x: I32 = 42;
//! # "#;
//! let mut libsl = LibSl::new();
//! let file = libsl.parse_file(file_name, contents)?;
//! println!("{:?}", libsl.decls[file.decls[0]]);
//! # Ok(())
//! # }
//! ```
//!
//! In addition to parsing, the crate allows converting an AST back to a LibSL source file. Since
//! most nodes need to print their children which they only refer to by an identifier, they do not
//! implement [`Display`][std::fmt::Display] directly, so you'll first need to call a `display`
//! method that takes a reference to [`LibSl`]:
//!
//! ```
//! # use libsl::LibSl;
//! #
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let file_name = "test.libsl".into();
//! # let contents = r#"libsl "1.0.0"; library test;
//! # val x: I32 = 42;
//! # "#;
//! let mut libsl = LibSl::new();
//! let file = libsl.parse_file(file_name, contents)?;
//! println!("{}", libsl.decls[file.decls[0]].display(&libsl));
//! # Ok(())
//! # }
//! ```

#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use loc::FileId;
use slotmap::{SlotMap, new_key_type};

pub mod ast;
pub mod export;
pub mod grammar;
pub mod loc;
mod parse;
#[cfg(feature = "serde")]
mod serialize;

new_key_type! {
    /// An [entity declaration][ast::Decl] identifier.
    pub struct DeclId;

    /// A [type expression][ast::TyExpr] identifier.
    pub struct TyExprId;

    /// An [expression][ast::Expr] identifier.
    pub struct ExprId;

    /// A [statement][ast::Stmt] identifier.
    pub struct StmtId;

    /// A [qualified access][ast::QualifiedAccess] identifier.
    pub struct QualifiedAccessId;
}

/// The top-level struct that stores all parsed AST nodes and allows access to them via an
/// identifier.
///
/// Conceptually corresponds to a single LibSL specification, potentially comprised of multiple
/// files.
#[derive(Debug, Default, Clone)]
pub struct LibSl {
    file_names: Vec<String>,

    /// Declaration AST nodes.
    pub decls: SlotMap<DeclId, ast::Decl>,

    /// Type expression AST nodes.
    pub ty_exprs: SlotMap<TyExprId, ast::TyExpr>,

    /// Expression AST nodes.
    pub exprs: SlotMap<ExprId, ast::Expr>,

    /// Statement AST nodes.
    pub stmts: SlotMap<StmtId, ast::Stmt>,

    /// Qualified access AST nodes.
    pub qualified_accesses: SlotMap<QualifiedAccessId, ast::QualifiedAccess>,
}

impl LibSl {
    /// Creates an empty LibSl specification.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the file name corresponding to the given `id`.
    pub fn filename_by_id(&self, id: FileId) -> &str {
        &self.file_names[id.0]
    }
}

/// A helper struct that bundles together `T` with a reference to [`LibSl`].
#[derive(Debug)]
pub struct LibSlNode<'a, T: 'a + ?Sized> {
    libsl: &'a crate::LibSl,
    inner: &'a T,
}

impl<'a, T: 'a + ?Sized> Clone for LibSlNode<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: 'a + ?Sized> Copy for LibSlNode<'a, T> {}

impl<'a, T: 'a + ?Sized> LibSlNode<'a, T> {
    /// Creates a new instance of [`LibSlNode`].
    pub fn new(inner: &'a T, libsl: &'a LibSl) -> Self {
        Self { libsl, inner }
    }

    /// Returns the inner value wrapped by `Self`.
    pub fn inner(&self) -> &'a T {
        self.inner
    }

    /// Returns the reference to [`LibSl`] stored in this struct.
    pub fn libsl(&self) -> &'a crate::LibSl {
        self.libsl
    }

    /// Maps the inner value using the function and wraps the result into [`LibSlNode`].
    pub fn map<F, R>(self, f: F) -> LibSlNode<'a, R>
    where
        F: FnOnce(&'a T) -> &'a R,
        R: 'a + ?Sized,
    {
        LibSlNode {
            libsl: self.libsl(),
            inner: f(self.inner()),
        }
    }
}

impl<'a, T: 'a> LibSlNode<'a, Option<T>> {
    /// Converts a `LibSlNode<Option<T>>` to `Option<LibSlNode<T>>`.
    pub fn transpose(self) -> Option<LibSlNode<'a, T>> {
        Some(LibSlNode {
            libsl: self.libsl(),
            inner: self.inner().as_ref()?,
        })
    }
}

/// Allows creating `WithLibSl` using method syntax.
pub trait WithLibSl {
    /// Creates a new [`LibSlNode`] instance for `Self`.
    fn with_libsl<'a>(&'a self, libsl: &'a crate::LibSl) -> LibSlNode<'a, Self> {
        LibSlNode { libsl, inner: self }
    }
}
