//! Provides types that allow referring to a part of a source file.
//!
//! Source location information is represented by the [`Loc`] enum, which acts like an
//! `Option<Span>`: [`Loc::Synthetic`] is used for nodes that are not represented in the source
//! file, whereas [`Loc::Span`] contains the [`Span`] corresponding to the node.

use std::num::NonZeroUsize;

use crate::WithLibSl;

/// A file identifier for use in [`Span`s][Span] to avoid lifetime parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub(crate) usize);

/// A contiguous range of bytes in a source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    /// The starting byte's offset.
    pub start: usize,

    /// A length of the span in bytes.
    pub len: usize,

    /// A file identifier.
    pub file_id: FileId,

    /// A line number, counted from 1.
    pub line: Option<NonZeroUsize>,

    /// A column number, counted from 1.
    pub col: Option<NonZeroUsize>,
}

impl WithLibSl for Span {}

/// A location in a source file.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Loc {
    /// No location information available, for example for synthesized constructs.
    #[default]
    Synthetic,

    /// The location corresponds to a span in the source file.
    Span(Span),
}

impl Loc {
    /// Returns `true` if the location is synthetic and has no span.
    pub fn is_synthetic(&self) -> bool {
        matches!(self, Self::Synthetic)
    }

    /// Returns the span associated with this location, or `None` if the location is synthetic.
    pub fn span(&self) -> Option<&Span> {
        match self {
            Self::Synthetic => None,
            Self::Span(span) => Some(span),
        }
    }
}

impl From<Span> for Loc {
    fn from(span: Span) -> Self {
        Loc::Span(span)
    }
}

impl From<Option<Span>> for Loc {
    fn from(span: Option<Span>) -> Self {
        span.map(Loc::Span).unwrap_or_default()
    }
}

impl From<Loc> for Option<Span> {
    fn from(loc: Loc) -> Self {
        loc.span().cloned()
    }
}

impl WithLibSl for Loc {}
