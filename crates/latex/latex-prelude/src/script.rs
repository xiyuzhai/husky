#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxScriptKind {
    Subscript,
    Superscript,
    Presubscript,
    Presuperscript,
    Overscript,
    Underscript,
}
