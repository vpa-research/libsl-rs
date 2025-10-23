//! Semantic analysis passes for LibSL.

mod load;
mod purity;

use slotmap::SparseSecondaryMap;

use crate::loc::FileId;
use crate::{DeclId, LibSl};

pub use crate::sema::load::{ImportCtx, LoadError};
pub use crate::sema::purity::check_pure;

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
}

impl<'ast> Sema<'ast> {
    fn from_import_ctx<L>(ctx: ImportCtx<'ast, '_, L>) -> Self {
        Self {
            libsl: ctx.libsl,
            imports: ctx.imports,
        }
    }
}
