//! A diagnostics module for reporting information during analyses.

use std::fmt::Display;

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
    ///
    /// Labels with synthetic locations may be ignored by the diagnostics reporter.
    pub labels: Vec<Label>,

    /// Ancillary messages.
    pub notes: Vec<String>,
}

impl Diag {
    /// Returns a new diagnostic with the `label` appended.
    pub fn with_label(mut self, label: Label) -> Self {
        self.labels.push(label);

        self
    }

    /// Returns a new diagnostic with the `note` appended.
    pub fn with_note(mut self, note: impl Display) -> Self {
        self.notes.push(note.to_string());

        self
    }

    /// Returns a new diagnostic by changing the severity level to the provided.
    pub fn with_level(mut self, level: Level) -> Self {
        self.level = level;

        self
    }

    /// Creates a builder to construct a diagnostic with the specified severity level.
    pub fn build(level: Level) -> DiagBuilder<false, false> {
        DiagBuilder {
            diag: Self {
                level,
                loc: Default::default(),
                msg: Default::default(),
                notes: Default::default(),
                labels: Default::default(),
            },
        }
    }

    /// Creates a builder to construct a diagnostic with the error severity level.
    pub fn err() -> DiagBuilder<false, false> {
        Self::build(Level::Err)
    }

    /// Creates a builder to construct a diagnostic with the warning severity level.
    pub fn warn() -> DiagBuilder<false, false> {
        Self::build(Level::Warn)
    }
}

/// A builder for [`Diag`].
///
/// You must set the primary location and the primary message before you can call [`build()`].
#[allow(missing_debug_implementations)]
pub struct DiagBuilder<const LOC_SET: bool, const MSG_SET: bool> {
    diag: Diag,
}

/// Methods to set the primary location.
impl<const LOC_SET: bool, const MSG_SET: bool> DiagBuilder<LOC_SET, MSG_SET> {
    /// Sets the primary location to `loc`.
    pub fn at(self, loc: impl Into<Loc>) -> DiagBuilder<true, MSG_SET> {
        DiagBuilder {
            diag: Diag {
                loc: Some(loc.into()),
                ..self.diag
            },
        }
    }

    /// Sets the primary location to `None`, making the diagnostic non-localized.
    pub fn without_loc(self) -> DiagBuilder<true, MSG_SET> {
        DiagBuilder {
            diag: Diag {
                loc: None,
                ..self.diag
            },
        }
    }
}

/// Methods to set the primary message.
impl<const LOC_SET: bool, const MSG_SET: bool> DiagBuilder<LOC_SET, MSG_SET> {
    /// Sets the primary message to `msg`.
    pub fn with_msg(self, msg: impl Display) -> DiagBuilder<LOC_SET, true> {
        DiagBuilder {
            diag: Diag {
                msg: msg.to_string(),
                ..self.diag
            },
        }
    }
}

/// Methods to change non-essential properties.
impl<const LOC_SET: bool, const MSG_SET: bool> DiagBuilder<LOC_SET, MSG_SET> {
    /// Appends a label to the resulting diagnostic.
    pub fn with_label(self, label: Label) -> Self {
        Self {
            diag: self.diag.with_label(label),
        }
    }

    /// Appends a note to the resulting diagnostic.
    pub fn with_note(self, note: impl Display) -> Self {
        Self {
            diag: self.diag.with_note(note),
        }
    }
}

/// Finalizing construction.
impl DiagBuilder<true, true> {
    /// Constructs a [diagnostic][Diag].
    ///
    /// You can only call this method if you have set both the primary location and the primary
    /// message.
    pub fn build(self) -> Diag {
        self.diag
    }
}

/// A code chunk optionally labelled with a message.
#[derive(Debug, Clone)]
pub struct Label {
    /// The location in the code.
    ///
    /// Labels with synthetic locations may be ignored by the diagnostics reporter.
    pub loc: Loc,

    /// The label's priority (primary or secondary).
    pub kind: LabelKind,

    /// The message attached to the label.
    pub msg: Option<String>,
}

impl Label {
    /// Constructs a new primary label.
    pub fn primary(loc: impl Into<Loc>) -> Self {
        Self {
            loc: loc.into(),
            kind: LabelKind::Primary,
            msg: None,
        }
    }

    /// Constructs a new secondary label.
    pub fn secondary(loc: impl Into<Loc>) -> Self {
        Self {
            loc: loc.into(),
            kind: LabelKind::Secondary,
            msg: None,
        }
    }

    /// Updates the message to `msg` and returns the new label.
    pub fn with_msg(self, msg: impl Display) -> Self {
        Self {
            msg: Some(msg.to_string()),
            ..self
        }
    }
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

/// A [DiagCtx] that ignores all diagnostics.
#[derive(Debug, Clone, Copy)]
pub struct DummyDiagCtx;

impl DiagCtx for DummyDiagCtx {
    fn emit(&mut self, _diag: Diag) {
        // ignore.
    }
}
