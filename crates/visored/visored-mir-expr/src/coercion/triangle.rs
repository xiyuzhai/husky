use visored_term::ty::VdType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdMirCoercionTriangle {
    pub src: VdType,
    pub mid: VdType,
    pub dst: VdType,
}

impl VdMirCoercionTriangle {
    pub fn new(src: VdType, mid: VdType, dst: VdType) -> Self {
        Self { src, mid, dst }
    }
}
