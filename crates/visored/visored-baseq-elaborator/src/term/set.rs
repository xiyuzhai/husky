use super::*;
use std::marker::PhantomData;
use visored_entity_path::path::set::VdSetPath;

#[enum_class::from_variants]
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqSetTerm<'sess> {
    Path(VdSetPath),
    Phantom(PhantomData<&'sess ()>),
}

impl<'sess> VdBsqSetTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqSetTerm::Path(path) => path.show_fmt(f),
            VdBsqSetTerm::Phantom(phantom_data) => todo!(),
        }
    }
}

impl<'db, 'sess> VdBsqSetTerm<'sess> {
    pub(crate) fn transcribe_data_and_ty(
        self,
        elaborator: &VdBsqElaboratorInner<'db, 'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        todo!()
    }
}
