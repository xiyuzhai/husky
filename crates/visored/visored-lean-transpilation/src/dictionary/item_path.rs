//! We use the word `translation` to mean the process is rather straightforward, which doesn't involve the complexity of arranging placeholders in super computation graph.
use super::*;
use lean_entity_path::LnItemPath;
use rustc_hash::FxHashMap;
use visored_entity_path::path::VdItemPath;

#[derive(Debug, PartialEq, Eq)]
pub enum VdItemPathTranslation {
    ItemPath(LnItemPath),
}

#[derive(Debug, PartialEq, Eq)]
pub struct VdItemPathDictionary {
    translations: FxHashMap<VdItemPath, VdItemPathTranslation>,
}

impl VdItemPathDictionary {
    pub fn new(
        translations: impl IntoIterator<Item = (VdItemPath, VdItemPathTranslation)>,
    ) -> Self {
        Self {
            translations: translations.into_iter().collect(),
        }
    }

    pub fn new_standard() -> Self {
        Self::new([
            (
                VdItemPath::NAT,
                VdItemPathTranslation::ItemPath(LnItemPath::NAT),
            ),
            (
                VdItemPath::INT,
                VdItemPathTranslation::ItemPath(LnItemPath::INT),
            ),
            (
                VdItemPath::RAT,
                VdItemPathTranslation::ItemPath(LnItemPath::RAT),
            ),
            (
                VdItemPath::REAL,
                VdItemPathTranslation::ItemPath(LnItemPath::REAL),
            ),
            (
                VdItemPath::COMPLEX,
                VdItemPathTranslation::ItemPath(LnItemPath::COMPLEX),
            ),
        ])
    }
}

impl VdItemPathDictionary {
    pub(crate) fn get(&self, item_path: VdItemPath) -> Option<&VdItemPathTranslation> {
        self.translations.get(&item_path)
    }
}
