use super::*;
use crate::coercion::VdBaseqCoercion;
use std::marker::PhantomData;
use visored_entity_path::theorem::VdTheoremPath;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBaseqHypothesisConstruction<'sess> {
    Sorry,
    Apply {
        path: VdTheoremPath,
        is_real_coercion: VdBaseqCoercion<'sess>,
    },
    Phantom(PhantomData<&'sess ()>),
}
