pub mod item_path;

use visored_item_path::path::VdItemPath;

use self::item_path::*;

pub struct VdLeanTranspilationDictionary {
    item_path_translation_table: VdItemPathTranslationTable,
}

impl VdLeanTranspilationDictionary {
    pub fn new_standard() -> Self {
        Self {
            item_path_translation_table: VdItemPathTranslationTable::new_standard(),
        }
    }
}

impl VdLeanTranspilationDictionary {
    pub fn item_path_translation(&self, item_path: VdItemPath) -> Option<&VdItemPathTranslation> {
        self.item_path_translation_table.get(item_path)
    }
}
