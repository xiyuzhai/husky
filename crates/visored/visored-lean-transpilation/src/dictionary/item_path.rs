//! We use the word `translation` to mean the process is rather straightforward, which doesn't involve the complexity of arranging placeholders in super computation graph.
use super::*;
use lean_item_path::LnItemPath;
use rustc_hash::FxHashMap;
use visored_item_path::path::VdItemPath;

#[derive(Debug, PartialEq, Eq)]
pub struct VdItemPathTranslationTable {
    translations: FxHashMap<VdItemPath, VdItemPathTranslation>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdItemPathTranslation {
    ItemPath(LnItemPath),
}

impl VdItemPathTranslationTable {
    pub fn new(
        translations: impl IntoIterator<Item = (VdItemPath, VdItemPathTranslation)>,
    ) -> Self {
        Self {
            translations: translations.into_iter().collect(),
        }
    }
    pub(crate) fn new_standard() -> Self {
        Self::new([(
            VdItemPath::NATURAL_NUMBER,
            VdItemPathTranslation::ItemPath(LnItemPath::NAT),
        )])
    }

    pub(crate) fn get(&self, item_path: VdItemPath) -> Option<&VdItemPathTranslation> {
        self.translations.get(&item_path)
    }
}
