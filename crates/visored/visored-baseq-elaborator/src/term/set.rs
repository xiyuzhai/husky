use super::*;
use std::marker::PhantomData;
use visored_entity_path::path::set::VdSetPath;

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
    pub(crate) fn expr(self, elr: &VdBsqElaboratorInner<'db, 'sess>) -> VdBsqExpr<'sess> {
        todo!()
    }
}
