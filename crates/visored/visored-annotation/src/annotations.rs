mod builder;

use crate::{
    annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation},
    *,
};
use builder::sparce::collect_from_sparse_annotations;
use husky_text_protocol::offset::TextOffsetRange;
use latex_token::{idx::LxTokenIdx, lane::LxTokenLane, storage::LxTokenStorage};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VdAnnotationRecord<A> {
    pub offset_range: TextOffsetRange,
    pub annotation: A,
}

pub type VdTokenAnnotationRecord = VdAnnotationRecord<VdTokenAnnotation>;
pub type VdSpaceAnnotationRecord = VdAnnotationRecord<VdSpaceAnnotation>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VdAnnotations {
    token_annotation_records: Vec<VdTokenAnnotationRecord>,
    space_annotation_records: Vec<VdSpaceAnnotationRecord>,
    /// the ith element is the annotation of the ith token
    token_annotations: Vec<Option<VdTokenAnnotation>>,
    /// the ith element is the annotation of the space before the ith token
    space_annotations: Vec<Option<VdSpaceAnnotation>>,
}

impl VdAnnotations {
    pub fn new(
        token_annotation_records: Vec<VdTokenAnnotationRecord>,
        space_annotation_records: Vec<VdSpaceAnnotationRecord>,
        token_storage: &LxTokenStorage,
    ) -> Self {
        // ad hoc
        let token_annotations =
            collect_token_annotations(LxTokenLane::Main, &token_annotation_records, token_storage);
        let space_annotations =
            collect_space_annotations(LxTokenLane::Main, &space_annotation_records, token_storage);
        Self {
            token_annotation_records,
            space_annotation_records,
            token_annotations,
            space_annotations,
        }
    }

    pub fn from_sparse<'a>(
        input: &'a str,
        token_annotations: impl IntoIterator<Item = ((&'a str, &'a str), VdTokenAnnotation)>,
        space_annotations: impl IntoIterator<Item = ((&'a str, &'a str), VdSpaceAnnotation)>,
        token_storage: &LxTokenStorage,
    ) -> Self {
        collect_from_sparse_annotations(
            input,
            token_annotations.into_iter(),
            space_annotations.into_iter(),
            token_storage,
        )
    }

    pub fn token_annotation_records(&self) -> &[VdTokenAnnotationRecord] {
        &self.token_annotation_records
    }

    pub fn space_annotation_records(&self) -> &[VdSpaceAnnotationRecord] {
        &self.space_annotation_records
    }

    pub fn token_annotation(&self, idx: LxTokenIdx) -> Option<VdTokenAnnotation> {
        self.token_annotations[idx.index()]
    }

    pub fn preceding_space_annotation(&self, idx: LxTokenIdx) -> Option<VdSpaceAnnotation> {
        self.space_annotations[idx.index()]
    }
}

fn collect_token_annotations(
    lane: LxTokenLane,
    token_annotation_records: &[VdTokenAnnotationRecord],
    token_storage: &LxTokenStorage,
) -> Vec<Option<VdTokenAnnotation>> {
    let mut entry_idx = 0;
    token_storage[lane]
        .iter()
        .map(|entry| {
            if entry_idx < token_annotation_records.len()
                && token_annotation_records[entry_idx].offset_range.start()
                    == entry.text_offset_range().start()
            {
                assert_eq!(
                    token_annotation_records[entry_idx].offset_range.end(),
                    entry.text_offset_range().end()
                );
                entry_idx += 1;
                Some(token_annotation_records[entry_idx - 1].annotation)
            } else {
                None
            }
        })
        .collect()
}

fn collect_space_annotations(
    lane: LxTokenLane,
    space_annotation_records: &[VdSpaceAnnotationRecord],
    token_storage: &LxTokenStorage,
) -> Vec<Option<VdSpaceAnnotation>> {
    let mut entry_idx = 0;
    token_storage[lane]
        .iter()
        .map(|entry| {
            let annotation = if entry_idx < space_annotation_records.len()
                && space_annotation_records[entry_idx].offset_range.start()
                    == entry.text_offset_range().start()
            {
                assert_eq!(
                    space_annotation_records[entry_idx].offset_range.end(),
                    entry.text_offset_range().end()
                );
                entry_idx += 1;
                Some(space_annotation_records[entry_idx - 1].annotation)
            } else {
                None
            };
            annotation
        })
        .collect()
}
