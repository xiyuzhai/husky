pub mod func_key;
pub mod item_path;

use self::{func_key::*, item_path::*};
use rustc_hash::FxHashMap;
use smallvec::{smallvec, SmallVec};
use visored_item_path::path::VdItemPath;
use visored_mir_expr::expr::application::{VdMirFunc, VdMirFuncKey};
use visored_term::instantiation::VdInstantiation;

#[derive(Debug, PartialEq, Eq)]
pub struct VdLeanDictionary {
    item_path_translation_table: VdItemPathDictionary,
    func_key_translation_table: VdFuncKeyDictionary,
}

impl VdLeanDictionary {
    pub fn new() -> Self {
        todo!()
    }

    pub fn new_standard(db: &::salsa::Db) -> Self {
        Self {
            item_path_translation_table: VdItemPathDictionary::new_standard(),
            func_key_translation_table: VdFuncKeyDictionary::new_standard(db),
        }
    }
}

impl VdLeanDictionary {
    pub fn item_path_translation(&self, item_path: VdItemPath) -> Option<&VdItemPathTranslation> {
        self.item_path_translation_table.get(item_path)
    }

    pub fn func_key_translation(&self, func_key: VdMirFuncKey) -> Option<&VdFuncKeyTranslation> {
        self.func_key_translation_table.get(func_key)
    }
}
