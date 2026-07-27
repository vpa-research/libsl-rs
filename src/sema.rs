//! Semantic analysis passes for LibSL.

pub mod def;
pub mod load;
pub mod purity;
pub mod resolve;
pub mod ty;
pub mod tyck;

use std::error::Error;
use std::fmt::{self, Display};

use slotmap::{SecondaryMap, SparseSecondaryMap};

use crate::diag::DiagCtx;
use crate::file::FileLoader;
use crate::sema::resolve::NameRes;
use crate::sema::tyck::TyCk;
use crate::{DeclId, FileId, LibSl};

pub use crate::sema::load::{ImportCtx, LoadError, LoadReason};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct SemaError;

impl Display for SemaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "semantic analysis failed")
    }
}

impl Error for SemaError {}

/// The result of a semantic analysis pass.
///
/// Usually the error information is absent from this type (set to `()`), since passes generally
/// output errors to a [`DiagCtx`] they take, which allows both emitting several errors at once and
/// attach more detailed information to each diagnostic.
///
/// When used in this way, the type acts as supercharged `bool` with the short-circuiting ability.
pub type Result<T = (), E = SemaError> = std::result::Result<T, E>;

/// A semantic analyzer for LibSL.
///
/// Semantic analysis is split into multiple steps (called passes). For this reason some fields may
/// not have correct values before you run a pass that initializes them.
#[allow(missing_debug_implementations)]
pub struct Sema<'ast> {
    /// The AST being analyzed.
    ///
    /// This field is public, so you can assign a reference to a different [`LibSl`] instance here,
    /// such as to modify it. However, all passes assume that all information collected in other
    /// fields corresponds to this AST. If you change the AST, you must update all other fields
    /// accordingly.
    pub libsl: &'ast LibSl,

    /// Maps each import declaration to the file its path resolves to.
    pub imports: SparseSecondaryMap<DeclId, FileId>,

    /// Maps each file to its load reason.
    pub load_reasons: SecondaryMap<FileId, LoadReason>,

    /// The results of name resolution.
    pub name_res: NameRes,

    /// The results of type checking.
    pub tyck: TyCk,
}

impl<'ast> Sema<'ast> {
    fn from_import_ctx<L: FileLoader>(ctx: ImportCtx<'ast, '_, L>) -> Self {
        Self {
            libsl: ctx.libsl,
            imports: ctx.imports,
            load_reasons: ctx.load_reasons,
            name_res: Default::default(),
            tyck: Default::default(),
        }
    }

    /// Performs all semantic analysis passes.
    pub fn analyze(&mut self, diag: &mut impl DiagCtx) -> Result {
        self.resolve_names(diag)?;
        self.tyck(diag)?;
        self.check_pure(diag)?;

        Ok(())
    }
}
