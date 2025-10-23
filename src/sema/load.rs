//! Recursive file loading with import resolution.

use std::error::Error;
use std::fmt::{self, Debug, Display};

use slotmap::SparseSecondaryMap;

use crate::file::FileLoader;
use crate::loc::FileId;
use crate::parse::ParseError;
use crate::sema::Sema;
use crate::{DeclId, LibSl};

/// Transitively loads and parses files and all their dependencies (specified using import
/// declarations).
pub struct ImportCtx<'ast, 'ld, L> {
    pub(super) libsl: &'ast mut LibSl,
    pub(super) loader: &'ld mut L,
    pub(super) imports: SparseSecondaryMap<DeclId, FileId>,
}

/// An enumeration of possible errors that may occur during file loading and import resolution.
#[derive(Debug, Clone)]
pub enum LoadError<L: FileLoader> {
    Parse(ParseError),
    File(L::Error),
}

impl<L: FileLoader> Display for LoadError<L>
where
    L::Error: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(e) => Display::fmt(e, f),
            Self::File(e) => Display::fmt(e, f),
        }
    }
}

impl<L: FileLoader> Error for LoadError<L>
where
    L: Debug,
    L::Error: Error + 'static,
{
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Parse(e) => Some(e),
            Self::File(e) => Some(e),
        }
    }
}

impl<'ast, 'ld, L: FileLoader> ImportCtx<'ast, 'ld, L> {
    /// Creates a new import context.
    pub fn new(libsl: &'ast mut LibSl, loader: &'ld mut L) -> Self {
        Self {
            libsl,
            loader,
            imports: Default::default(),
        }
    }

    /// Loads a file by its path.
    pub fn load(&mut self, path: &str) -> Result<FileId, LoadError<L>> {
        todo!()
    }

    /// Creates a semantic analyzer instance for the loaded files.
    pub fn into_sema(self) -> Sema<'ast> {
        Sema::from_import_ctx(self)
    }
}
