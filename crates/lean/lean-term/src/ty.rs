use crate::term::LnTerm;
use crate::*;
use lean_entity_path::LnItemPath;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LnType(LnTerm);

impl LnType {
    // TODO: check it??
    pub fn new_item_path(path: LnItemPath) -> Self {
        Self(LnTerm::new_item_path(path))
    }

    pub fn show(&self) -> String {
        self.0.show()
    }
}
