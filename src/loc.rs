/// A contiguous range of bytes in a source file.
///
/// On its own, a span stores just a byte offset and a length.
/// The mapping between the span and its line/column information, as well as the source file's name,
/// is maintained by a source map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: usize,
    len: usize,
}

/// A location in a source file.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
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
    pub fn span(&self) -> Option<Span> {
        match *self {
            Self::Synthetic => None,
            Self::Span(span) => Some(span),
        }
    }
}

impl From<Option<Span>> for Loc {
    fn from(span: Option<Span>) -> Self {
        span.map(Loc::Span).unwrap_or_default()
    }
}

impl From<Loc> for Option<Span> {
    fn from(loc: Loc) -> Self {
        loc.span()
    }
}
