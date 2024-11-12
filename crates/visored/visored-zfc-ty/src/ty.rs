use smallvec::SmallVec;
use visored_coword::namae::VdNamae;

pub struct VdZfcType {
    data: VdZfcTypeData,
    refinements: SmallVec<[(); 2]>,
}

pub enum VdZfcTypeData {
    Named(VdNamae), // TODO: do we need a path here?
}
