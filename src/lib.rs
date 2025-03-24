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
//! # let contents = r#"libsl "1.0.0" library test;
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
//! # let contents = r#"libsl "1.0.0" library test;
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
//! # let contents = r#"libsl "1.0.0" library test;
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
pub mod dump;
pub mod grammar;
pub mod loc;
mod parse;

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
