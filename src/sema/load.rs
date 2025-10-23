//! Recursive file loading with import resolution.

use std::collections::HashMap;
use std::error::Error;
use std::fmt::{self, Debug, Display};

use slotmap::SparseSecondaryMap;

use crate::ast;
use crate::file::FileLoader;
use crate::loc::FileId;
use crate::parse::ParseError;
use crate::sema::Sema;
use crate::{DeclId, LibSl};

#[derive(Debug)]
struct LoadReq {
    path: String,
    import_decl_id: Option<DeclId>,
}

/// Transitively loads and parses files and all their dependencies (specified using import
/// declarations).
#[derive(Debug)]
pub struct ImportCtx<'ast, 'ld, L: FileLoader> {
    pub(super) libsl: &'ast mut LibSl,
    loader: &'ld mut L,
    pub(super) imports: SparseSecondaryMap<DeclId, FileId>,
    load_reqs: Vec<LoadReq>,
    files: HashMap<L::CanonicalName, FileId>,
}

/// An enumeration of possible errors that may occur during file loading and import resolution.
// TODO: store the load chain.
#[derive(Debug, Clone)]
pub enum LoadError<L: FileLoader> {
    /// A parsing error.
    Parse(ParseError),

    /// A file loading error.
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
            load_reqs: Default::default(),
            files: Default::default(),
        }
    }

    /// Loads a file by its path.
    pub fn load(&mut self, path: &str) -> Result<FileId, LoadError<L>> {
        self.load_reqs.push(LoadReq {
            path: path.to_string(),
            import_decl_id: None,
        });

        self.process_loads()
    }

    /// Creates a semantic analyzer instance for the loaded files.
    pub fn into_sema(self) -> Sema<'ast> {
        Sema::from_import_ctx(self)
    }

    fn process_loads(&mut self) -> Result<FileId, LoadError<L>> {
        let mut root_file_id: Option<FileId> = None;

        while let Some(req) = self.load_reqs.pop() {
            let f = self.loader.load(&req.path).map_err(LoadError::File)?;

            let file_id = if let Some(&file_id) = self.files.get(&f.canonical_name) {
                file_id
            } else {
                let file_id = self
                    .libsl
                    .parse_file(f.canonical_name.to_string(), f.contents)
                    .map_err(LoadError::Parse)?;
                self.files.insert(f.canonical_name.clone(), file_id);

                for &decl_id in &self.libsl.file_by_id(file_id).decls {
                    let decl = &self.libsl.decls[decl_id];

                    if let ast::DeclKind::Import(import) = &decl.kind {
                        self.load_reqs.push(LoadReq {
                            path: import.path.clone(),
                            import_decl_id: Some(decl.id),
                        });
                    }
                }

                file_id
            };

            if let Some(import_decl_id) = req.import_decl_id {
                self.imports.insert(import_decl_id, file_id);
            } else {
                debug_assert!(root_file_id.is_none(), "multiple root load requests found");
                root_file_id = Some(file_id);
            }
        }

        Ok(root_file_id.expect("no root load request found"))
    }
}
