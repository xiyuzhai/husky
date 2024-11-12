#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FileExtensionConfig {
    Markdown,
    Rust,
}

impl FileExtensionConfig {
    pub fn str(self) -> &'static str {
        match self {
            FileExtensionConfig::Markdown => "md",
            FileExtensionConfig::Rust => "rs",
        }
    }
}
