//! File loading and name canonicalization.

use std::collections::HashMap;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::path::PathBuf;
use std::{fs, io};

use relative_path::{PathExt, RelativePathBuf};

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
pub trait CanonicalName: Debug + Display + Clone + Eq + Hash {}

/// The result of loading a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedFile<'a, C> {
    /// The canonical name for this file.
    pub canonical_name: C,

    /// The contents of the file.
    pub contents: &'a str,
}

/// Implements loading files by path and name canonicalization.
///
/// LibSL files may refer to other files by their paths in `import` and `include` declarations.
/// Furthermore, different paths may name the same file, which must only be loaded once.
/// This trait maps paths to canonical names (unique for each individual file) and reads files into
/// memory.
pub trait FileLoader {
    /// The canonical name type this file loader uses.
    type CanonicalName: CanonicalName;

    /// The type of an error that may be produced while loading a file.
    type Error;

    /// Resolves the `path` to a file, looks up its canonical name, and reads its contents to
    /// memory.
    fn load<'a>(
        &'a mut self,
        path: &str,
    ) -> Result<LoadedFile<'a, Self::CanonicalName>, Self::Error>;

    /// Returns the contents of an already-loaded file by its canonical name.
    fn get<'a>(&'a self, name: &Self::CanonicalName) -> &'a str;
}

/// A [`FileLoader`] that loads files from the file system.
///
/// Paths are treated as file system paths, and are resolved relative to a base directory.
#[derive(Debug)]
pub struct FsFileLoader {
    base_dir: PathBuf,
    loaded_files: HashMap<RelativePathBuf, String>,
}

impl FsFileLoader {
    /// Creates a new instance of [`FsFileLoader`] that searches for files relative to the
    /// `base_dir`.
    pub fn new(base_dir: PathBuf) -> io::Result<Self> {
        Ok(Self {
            base_dir: base_dir.canonicalize()?,
            loaded_files: Default::default(),
        })
    }
}

/// A [`CanonicalName`] based on the relative path.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PathCanonicalName(RelativePathBuf);

impl Display for PathCanonicalName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl CanonicalName for PathCanonicalName {}

impl FileLoader for FsFileLoader {
    type CanonicalName = PathCanonicalName;
    type Error = io::Error;

    fn load<'a>(
        &'a mut self,
        path: &str,
    ) -> Result<LoadedFile<'a, Self::CanonicalName>, Self::Error> {
        let path = self.base_dir.join(path).canonicalize()?;
        let relative_path = path.relative_to(&self.base_dir).map_err(io::Error::other)?;

        if self.loaded_files.contains_key(&relative_path) {
            let (relative_path, contents) =
                self.loaded_files.get_key_value(&relative_path).unwrap();
            let canonical_name = PathCanonicalName(relative_path.clone());

            return Ok(LoadedFile {
                canonical_name,
                contents,
            });
        }

        let path = relative_path.to_path(&self.base_dir);
        let contents = fs::read_to_string(path)?;
        self.loaded_files.insert(relative_path.clone(), contents);
        let (relative_path, contents) = self.loaded_files.get_key_value(&relative_path).unwrap();
        let canonical_name = PathCanonicalName(relative_path.clone());

        Ok(LoadedFile {
            canonical_name,
            contents,
        })
    }

    fn get<'a>(&'a self, name: &Self::CanonicalName) -> &'a str {
        self.loaded_files.get(&name.0).unwrap()
    }
}
