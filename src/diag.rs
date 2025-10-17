//! A diagnostics module for reporting information during analyses.

use crate::loc::Loc;

/// A diagnostic message's severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    /// An error severity level.
    Err,

    /// A warning severity level.
    Warn,
}

/// A diagnostic message.
///
/// The diagnostic is composed of the primary and secondary information. The primary part conveys
/// the essence of the message. The secondary part expands on that to provide more context and help.
///
/// The primary part includes the level, the primary location, the primary message, and primary
/// labels. The secondary part is comprised of notes and secondary labels.
#[derive(Debug, Clone)]
pub struct Diag {
    /// The diagnostic's severity level.
    pub level: Level,

    /// The primary location associated with the diagnostic (namely, its primary message and notes).
    ///
    /// The value is interpreted as follows:
    /// - `None` means the diagnostic is not localized at all.
    /// - `Some(Loc::Synthetic)` means the diagnostic corresponds to synthetic code.
    /// - `Some(Loc::Span(_))` means the diagnostic corresponds to user code.
    pub loc: Option<Loc>,

    /// The primary message.
    ///
    /// It should be concise but self-sufficient. In particular, it should make sense without notes
    /// and labels.
    pub msg: String,

    /// Spans of code labelled with explanatory messages.
    pub labels: Vec<Label>,

    /// Ancillary messages.
    pub notes: Vec<String>,
}

/// A code chunk optionally labelled with a message.
#[derive(Debug, Clone)]
pub struct Label {
    /// The location in the code.
    pub loc: Loc,

    /// The label's priority (primary or secondary).
    pub kind: LabelKind,

    /// The message attached to the label.
    pub msg: Option<String>,
}

/// The priority of a [Label].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LabelKind {
    /// The primary label priority.
    Primary,

    /// The secondary label priority.
    Secondary,
}

/// Reports [diagnostics][Diag] produced by analyses.
pub trait DiagCtx {
    /// Records a diagnostic for reporting.
    fn emit(&mut self, diag: Diag);
}
