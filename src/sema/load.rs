//! Recursive file loading with import resolution.

use std::collections::HashMap;
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::num::NonZeroUsize;

use slotmap::{SecondaryMap, SparseSecondaryMap};

use crate::diag::{Diag, Label};
use crate::file::FileLoader;
use crate::loc::{Loc, Span};
use crate::parse::{ParseError, Radix};
use crate::sema::Sema;
use crate::{DeclId, LibSl};
use crate::{FileId, ast};

/// Describes how a file was loaded.
#[derive(Debug, Clone)]
pub enum LoadReason {
    /// The file was loaded due to an import declaration with the given [`DeclId`].
    Imported(DeclId),

    /// The file was loaded due to an explicit top-level request for the given path.
    TopLevel(String),
}

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
    pub(super) load_reasons: SecondaryMap<FileId, LoadReason>,
}

/// An enumeration of possible errors that may occur during file loading and import resolution.
#[derive(Debug, Clone)]
pub enum LoadError<L: FileLoader> {
    /// A parsing error.
    Parse {
        /// The path to the file that caused the error.
        path: String,

        /// The canonical name of the file that caused the error.
        canonical_name: L::CanonicalName,

        /// The underlying cause.
        err: ParseError,

        /// The reason this file was being loaded.
        load_reason: LoadReason,
    },

    /// A file loading error.
    File {
        /// The path to the file that caused the error.
        path: String,

        /// The underlying cause.
        err: L::Error,

        /// The reason this file was being loaded.
        load_reason: LoadReason,
    },
}

struct LineCache<L: FileLoader> {
    line_offsets: HashMap<L::CanonicalName, Vec<usize>>,
}

impl<L: FileLoader> Default for LineCache<L> {
    fn default() -> Self {
        Self {
            line_offsets: Default::default(),
        }
    }
}

fn compute_line_offsets(contents: &str) -> Vec<usize> {
    contents
        .match_indices('\n')
        .map(|(idx, _)| idx + 1)
        .collect()
}

fn search_line(line_offsets: &[usize], line: NonZeroUsize) -> Option<usize> {
    let Some(idx) = line.get().checked_sub(2) else {
        return Some(0);
    };

    line_offsets.get(idx).copied()
}

impl<L: FileLoader> LineCache<L> {
    fn line_pos(
        &mut self,
        loader: &L,
        canonical_name: &L::CanonicalName,
        line: NonZeroUsize,
    ) -> Option<usize> {
        let entry;
        let line_offsets = match self.line_offsets.get(canonical_name) {
            Some(line_offsets) => line_offsets,

            None => {
                let contents = loader.get(canonical_name);
                let line_offsets = compute_line_offsets(contents);

                entry = self
                    .line_offsets
                    .entry(canonical_name.clone())
                    .insert_entry(line_offsets);

                entry.get()
            }
        };

        search_line(line_offsets, line)
    }

    fn line_col_pos(
        &mut self,
        loader: &L,
        canonical_name: &L::CanonicalName,
        line: NonZeroUsize,
        col: NonZeroUsize,
    ) -> Option<usize> {
        let contents = loader.get(canonical_name);
        let line_pos = self.line_pos(loader, canonical_name, line)?;

        contents[line_pos..]
            .char_indices()
            .nth(col.get() - 1)
            .map(|(idx, _)| idx)
    }
}

fn add_import_chain_notes(diag: &mut Diag, sema: &Sema<'_>, load_reason: &LoadReason) {
    // this variable unifies the lifetimes of `sema` and `load_reason`, avoiding cluttering the
    // function's signature with pointless lifetime annotations.
    let mut load_reason = load_reason;

    while let &LoadReason::Imported(decl_id) = load_reason {
        let file_id = match &sema.libsl.decls[decl_id].loc {
            Loc::Span(span) => span.file_id,
            _ => break,
        };

        diag.labels.push(
            Label::secondary(sema.libsl.decls[decl_id].loc.clone()).with_msg("imported here"),
        );

        load_reason = &sema.load_reasons[file_id];
    }
}

fn parse_error_to_diag<L: FileLoader>(
    e: &LoadError<L>,
    mut line_cache: LineCache<L>,
    loader: &L,
    sema: &Sema<'_>,
) -> Diag {
    let LoadError::Parse {
        canonical_name,
        err,
        load_reason,
        ..
    } = e
    else {
        unreachable!();
    };

    let (file_id, line, col, len) = match *err {
        ParseError::Syntax {
            file_id,
            line,
            col,
            len,
            ..
        }
        | ParseError::Int {
            file_id,
            line,
            col,
            len,
            ..
        } => (file_id, line, col, len),
    };

    let start = line
        .zip(col)
        .and_then(|(line, col)| line_cache.line_col_pos(loader, canonical_name, line, col))
        .unwrap_or(0);
    let span = Span {
        start,
        len,
        file_id,
        line,
        col,
    };

    let diag = Diag::err().at(span.clone());
    let diag = match err {
        ParseError::Syntax { msg, .. } => {
            diag.with_msg(format_args!("encountered a syntax error: {msg}"))
        }

        ParseError::Int { radix, inner, .. } => diag.with_msg(format_args!(
            "could not parse {article} {radix} integer literal: {inner}",
            article = if *radix == Radix::Octal { "an" } else { "a" },
        )),
    };

    let mut diag = diag.with_label(Label::primary(span)).build();
    add_import_chain_notes(&mut diag, sema, load_reason);

    diag
}

fn file_error_to_diag<L: FileLoader>(e: &LoadError<L>, sema: &Sema<'_>) -> Diag
where
    L::Error: Display,
{
    let LoadError::File {
        path,
        err,
        load_reason,
        ..
    } = e
    else {
        unreachable!()
    };

    let mut diag = Diag::err()
        .without_loc()
        .with_msg(format!("could not load `{path}`: {err}"))
        .build();

    add_import_chain_notes(&mut diag, sema, load_reason);

    diag
}

impl<L: FileLoader> LoadError<L>
where
    L::Error: Display,
{
    /// Creates a new diagnostic corresponding to this error.
    pub fn to_diag(&self, loader: &L, sema: &Sema<'_>) -> Diag {
        let line_cache = LineCache::default();

        match self {
            Self::Parse { .. } => parse_error_to_diag(self, line_cache, loader, sema),
            Self::File { .. } => file_error_to_diag(self, sema),
        }
    }
}

impl<L: FileLoader> Display for LoadError<L>
where
    L::Error: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse { .. } => write!(f, "could not parse a file"),
            Self::File { .. } => write!(f, "could not load a file"),
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
            Self::Parse { err, .. } => Some(err),
            Self::File { err, .. } => Some(err),
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
            load_reasons: Default::default(),
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
            let load_reason = match req.import_decl_id {
                Some(decl_id) => LoadReason::Imported(decl_id),
                None => LoadReason::TopLevel(req.path.clone()),
            };

            let f = self.loader.load(&req.path).map_err(|err| LoadError::File {
                path: req.path.clone(),
                err,
                load_reason: load_reason.clone(),
            })?;

            let file_id = if let Some(&file_id) = self.files.get(&f.canonical_name) {
                file_id
            } else {
                let file_id = self
                    .libsl
                    .parse_file(f.canonical_name.to_string(), f.contents)
                    .map_err(|err| LoadError::Parse {
                        path: req.path.clone(),
                        canonical_name: f.canonical_name.clone(),
                        err,
                        load_reason: load_reason.clone(),
                    })?;
                self.files.insert(f.canonical_name.clone(), file_id);

                self.load_reasons.insert(file_id, load_reason);

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
