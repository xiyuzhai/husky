use super::LxEnvironmentSignature;
use crate::path::{
    menu::{LxEnvironmentPathMenu, LX_ENVIRONMENT_PATH_MENU},
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

    pub fn new_default() -> Self {
        let LxEnvironmentPathMenu {
            document,
            example,
            proof,
            remark,
            definition,
            theorem,
            lemma,
            corollary,
            proposition,
            align,
            array,
            matrix,
            cases,
            equation,
            figure,
            table,
        } = *LX_ENVIRONMENT_PATH_MENU;
        Self::new([
            (document, (&[LxMode::Root], LxMode::Rose)),
            // theorems
            (example, (&[LxMode::Rose], LxMode::Rose)),
            (proof, (&[LxMode::Rose], LxMode::Rose)),
            (remark, (&[LxMode::Rose], LxMode::Rose)),
            (definition, (&[LxMode::Rose], LxMode::Rose)),
            (theorem, (&[LxMode::Rose], LxMode::Rose)),
            (lemma, (&[LxMode::Rose], LxMode::Rose)),
            (corollary, (&[LxMode::Rose], LxMode::Rose)),
            (proposition, (&[LxMode::Rose], LxMode::Rose)),
            // math
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
