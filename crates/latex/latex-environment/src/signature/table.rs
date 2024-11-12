use super::LxEnvironmentSignature;
use crate::path::{
    menu::{lx_environment_menu, LxEnvironmentMenu},
    LxEnvironmentName, LxEnvironmentPath,
};
use latex_prelude::mode::LxMode;
use rustc_hash::FxHashMap;

pub struct LxEnvironmentSignatureTable {
    signatures: FxHashMap<LxEnvironmentName, LxEnvironmentSignature>,
}

impl LxEnvironmentSignatureTable {
    pub fn new<'a, const N: usize>(
        signatures: [(LxEnvironmentPath, (&'a [LxMode], LxMode)); N],
    ) -> Self {
        Self {
            signatures: signatures
                .into_iter()
                .map(|(path, (allowed_modes, body_mode))| {
                    (
                        path.name(),
                        LxEnvironmentSignature::new(path, allowed_modes, body_mode),
                    )
                })
                .collect(),
        }
    }

    pub fn new_default(db: &::salsa::Db) -> Self {
        let LxEnvironmentMenu {
            align,
            array,
            matrix,
            cases,
            equation,
            figure,
            table,
        } = *lx_environment_menu(db);
        Self::new([
            (align, (&[LxMode::Math, LxMode::Rose], LxMode::Math)),
            (array, (&[LxMode::Math], LxMode::Math)),
            (matrix, (&[LxMode::Math], LxMode::Math)),
            (cases, (&[LxMode::Math], LxMode::Math)),
            (equation, (&[LxMode::Rose], LxMode::Math)),
        ])
    }
}

impl LxEnvironmentSignatureTable {
    pub fn signature(&self, name: LxEnvironmentName) -> Option<LxEnvironmentSignature> {
        self.signatures.get(&name).copied()
    }
}
