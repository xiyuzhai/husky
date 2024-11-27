pub(crate) mod crate_decl;
pub(crate) mod item_decl;
pub(crate) mod item_defn;

use crate::*;
use husky_entity_path::path::{ItemPath, ItemPathId};
use husky_regional_token::RegionalTokenIdx;
use husky_text_protocol::range::TextPositionRange;
use husky_vfs::path::module_path::ModulePath;
use is::Is;

#[derive(Debug, PartialEq, Eq)]
pub struct InlayHint {
    pub position: InlayHintPosition,
    pub label: InlayHintLabel,
    pub kind: InlayHintKind,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum InlayHintPosition {
    EndOfRegionSpaced,
}

#[derive(Debug, PartialEq, Eq)]
pub enum InlayHintLabel {
    String(String),
    LabelParts(Vec<InlayHintLabelPart>),
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct InlayHintLabelPart {
    /// The value of this label part.
    pub value: String,

    /// The tooltip text when you hover over this label part. Depending on
    /// the client capability `inlayHint.resolveSupport` clients might resolve
    /// this property late using the resolve request.
    pub tooltip: Option<InlayHintLabelPartTooltip>,

    /// An optional source code location that represents this
    /// label part.
    ///
    /// The editor will use this location for the hover and for code navigation
    /// features: This part will become a clickable link that resolves to the
    /// definition of the symbol at the given location (not necessarily the
    /// location itself), it shows the hover that shows at the given location,
    /// and it shows a context menu with further code navigation commands.
    ///
    /// Depending on the client capability `inlayHint.resolveSupport` clients
    /// might resolve this property late using the resolve request.
    pub location: Option<InlayHintLocation>,

    /// An optional command for this label part.
    ///
    /// Depending on the client capability `inlayHint.resolveSupport` clients
    /// might resolve this property late using the resolve request.
    pub command: Option<Command>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct InlayHintLabelPartTooltip;

#[derive(Debug, PartialEq, Eq)]
pub struct InlayHintLocation {
    module_path: ModulePath,
    range: TextPositionRange,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Command {
    /// Title of the command, like `save`.
    pub title: String,
    /// The identifier of the actual command handler.
    pub command: String,
    /// Arguments that the command handler should be
    /// invoked with.
    pub arguments: Option<Vec<serde_json::Value>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum InlayHintKind {
    TypeAnnotation,
    ParameterIdent,
    AttrInferred,
}
