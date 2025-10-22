//! File loading and name canonicalization.

use std::collections::HashMap;
use std::fmt::{self, Display};
use std::hash::Hash;
use std::path::{Path, PathBuf};
use std::{fs, io};

use relative_path::{PathExt, RelativePath, RelativePathBuf};

/// The canonical name of a file.
///
/// The canonical name must satisfy three laws:
///
/// 1. If two paths refer to the same file, the canonical path **must be the same**.
/// 2. No two different files may have the same canonical name.
/// 3. The [`Eq`] and [`Hash`] impls must uphold their respective laws.
///
/// While breaking these laws won't lead to unsafety, it will cause suprising behavior.
///
/// The [`Display`] representation is used to user-visible messages (such as diagnostics).
pub trait CanonicalName<'a>: Display + Eq + Hash {}

/// The result of loading a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadedFile<'a, C> {
    /// The file has already been loaded previously and assigned a canonical name.
    AlreadyLoaded {
        /// The canonical name for this file.
        canonical_name: C,

        /// The contents of the file.
        contents: &'a str,
    },

    /// The file has not been loaded previously.
    New {
        /// The canonical name for this file.
        canonical_name: C,

        /// The contents of the file.
        contents: &'a str,
    },
}

/// Implements loading files by path and name canonicalization.
///
/// LibSL files may refer to other files by their paths in `import` and `include` declarations.
/// Furthermore, different paths may name the same file, which must only be loaded once.
/// This trait maps paths to canonical names (unique for each individual file) and reads files into
/// memory.
pub trait FileLoader {
    /// The canonical name type this file loader uses.
    type CanonicalName<'a>: CanonicalName<'a>
    where
        Self: 'a;

    /// The type of an error that may be produced while loading a file.
    type Error;

    /// Resolves the `path` to a file, looks up its canonical name, and reads its contents to
    /// memory.
    fn load<'a>(
        &'a mut self,
        path: &str,
    ) -> Result<LoadedFile<'a, Self::CanonicalName<'a>>, Self::Error>;

    /// Returns the contents of an already-loaded file by its canonical name.
    fn get<'a>(&'a self, name: Self::CanonicalName<'a>) -> &'a str;
}

/// A [`FileLoader`] that loads files from the file system.
///
/// Paths are treated as file system paths, and are resolved relative to a base directory.
#[derive(Debug)]
pub struct FsFileLoader {
    base_dir: PathBuf,
    loaded_files: HashMap<RelativePathBuf, String>,
}

/// A [`CanonicalName`] based on the relative path.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PathCanonicalName<'a>(&'a RelativePath);

impl Display for PathCanonicalName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> CanonicalName<'a> for PathCanonicalName<'a> {}

impl FileLoader for FsFileLoader {
    type CanonicalName<'a> = PathCanonicalName<'a>;
    type Error = io::Error;

    fn load<'a>(
        &'a mut self,
        path: &str,
    ) -> Result<LoadedFile<'a, Self::CanonicalName<'a>>, Self::Error> {
        let path = Path::new(path).canonicalize()?;
        let relative_path = path
            .relative_to(&self.base_dir)
            .map_err(|e| io::Error::other(e))?;

        if self.loaded_files.contains_key(&relative_path) {
            let (relative_path, contents) =
                self.loaded_files.get_key_value(&relative_path).unwrap();
            let canonical_name = PathCanonicalName(relative_path);

            return Ok(LoadedFile::AlreadyLoaded {
                canonical_name,
                contents,
            });
        }

        let path = relative_path.to_path(&self.base_dir);
        let contents = fs::read_to_string(path)?;
        self.loaded_files.insert(relative_path.clone(), contents);
        let (relative_path, contents) = self.loaded_files.get_key_value(&relative_path).unwrap();
        let canonical_name = PathCanonicalName(relative_path);

        Ok(LoadedFile::New {
            canonical_name,
            contents,
        })
    }

    fn get<'a>(&'a self, name: Self::CanonicalName<'a>) -> &'a str {
        self.loaded_files.get(name.0).unwrap()
    }
}
