use crate::*;
use husky_text_protocol::{
    position::{TextLine, TextPosition},
    range::TextPositionRange,
};
use ref_index::RefIndex;
use std::ops::{Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};

impl<'a> Text<'a> {
    pub fn text_within<R>(self, range: R) -> &'a str
    where
        Self: RefIndex<'a, R, Output = str>,
    {
        self.ref_index(range)
    }
}

#[cfg(test)]
#[track_caller]
pub(crate) fn run_index_test_on_text<I>(input: &str, index: I, expected: &str)
where
    for<'a> Text<'a>: RefIndex<'a, I, Output = str>,
{
    run_test_on_text(
        input,
        #[track_caller]
        |text| assert_eq!(text.ref_index(index), expected),
    )
}

impl<'a> RefIndex<'a, Range<(u32, u32)>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range: Range<(u32, u32)>) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range(range)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_u32_pair_range_works() {
    let t = run_index_test_on_text::<Range<(u32, u32)>>;
    t("hello", (0, 1)..(0, 3), "el");
}

impl<'a> RefIndex<'a, TextPositionRange> for Text<'a> {
    type Output = str;

    fn ref_index(self, range: TextPositionRange) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range(range)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_text_range_works() {
    let t = run_index_test_on_text::<TextPositionRange>;
    t("hello", ((0, 1)..(0, 3)).into(), "el");
}

impl<'a> RefIndex<'a, RangeFrom<TextPosition>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_from: RangeFrom<TextPosition>) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range_from(range_from)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_from_text_position_works() {
    let t = run_index_test_on_text::<RangeFrom<TextPosition>>;
    t("hello", ((0, 1).into()).., "ello");
}

#[test]
#[should_panic]
pub(crate) fn range_from_text_position_fails() {
    let t = run_index_test_on_text::<RangeFrom<TextPosition>>;
    t("hello\n", ((1, 1).into()).., "ello");
}

impl<'a> RefIndex<'a, RangeTo<TextPosition>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_to: RangeTo<TextPosition>) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range_to(range_to)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_to_text_position_works() {
    let t = run_index_test_on_text::<RangeTo<TextPosition>>;
    t("hello", ..((0, 3).into()), "hel");
}

// TODO: inclusive text position might be tricky because a char might span multiple bytes

// impl<'a> RefIndex<'a, RangeInclusive<TextPosition>> for Text<'a> {
//     type Output = str;

//     fn ref_index(self, range_inclusive: RangeInclusive<TextPosition>) -> &'a Self::Output {
//         &self.raw[self.line_map.offset_range_inclusive(range_inclusive)]
//     }
// }

// #[test]
// pub(crate) fn text_ref_index_by_range_inclusive_text_position_works() {
//     let t = run_index_test_on_text::<RangeInclusive<TextPosition>>;
//     t("hello", ((0, 0).into())..=((0, 2).into()), "hel");
// }

// impl<'a> RefIndex<'a, RangeToInclusive<TextPosition>> for Text<'a> {
//     type Output = str;

//     fn ref_index(self, range_to_inclusive: RangeToInclusive<TextPosition>) -> &'a Self::Output {
//         &self.raw[self.line_map.offset_range_to_inclusive(range_to_inclusive)]
//     }
// }

// #[test]
// pub(crate) fn text_ref_index_by_range_to_inclusive_text_position_works() {
//     let t = run_index_test_on_text::<RangeToInclusive<TextPosition>>;
//     t("hello", ..=((0, 2).into()), "hel");
// }

impl<'a> RefIndex<'a, TextLine> for Text<'a> {
    type Output = str;

    fn ref_index(self, range: TextLine) -> &'a Self::Output {
        &self.raw[self.line_map.text_line_offset_range(range)]
    }
}

impl<'a> RefIndex<'a, Range<TextLine>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range: Range<TextLine>) -> &'a Self::Output {
        &self.raw[self.line_map.text_line_range_offset_range(range)]
    }
}

impl<'a> RefIndex<'a, RangeFrom<TextLine>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_from: RangeFrom<TextLine>) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range_from_text_line(range_from)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_from_text_line_works() {
    let t = run_index_test_on_text::<RangeFrom<TextLine>>;
    t("hello", (0.into()).., "hello");
    t("hello\nworld", (0.into()).., "hello\nworld");
    t("hello\nworld", (1.into()).., "world");
}

impl<'a> RefIndex<'a, RangeTo<TextLine>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_to: RangeTo<TextLine>) -> &'a Self::Output {
        &self.raw[self.line_map.offset_range_to_text_line(range_to)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_to_text_line_works() {
    let t = run_index_test_on_text::<RangeTo<TextLine>>;
    t("hello", ..(0.into()), "");
    t("hello\nworld", ..(0.into()), "");
    t("hello\nworld", ..(1.into()), "hello\n");
    t("hello\nworld", ..(2.into()), "hello\nworld");
}

impl<'a> RefIndex<'a, RangeInclusive<TextLine>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_inclusive: RangeInclusive<TextLine>) -> &'a Self::Output {
        &self.raw[self
            .line_map
            .offset_range_inclusive_text_line(range_inclusive)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_inclusive_text_line_works() {
    let t = run_index_test_on_text::<RangeInclusive<TextLine>>;
    t("hello", (0.into())..=(0.into()), "hello");
    t("hello\nworld", (0.into())..=(0.into()), "hello\n");
    t("hello\nworld", (0.into())..=(1.into()), "hello\nworld");
    t("hello\nworld\n", (0.into())..=(2.into()), "hello\nworld\n");
}

#[test]
#[should_panic]
pub(crate) fn text_ref_index_by_range_inclusive_text_line_fails() {
    let t = run_index_test_on_text::<RangeInclusive<TextLine>>;
    t("hello\nworld", (0.into())..=(2.into()), "hello\nworld");
}

impl<'a> RefIndex<'a, RangeToInclusive<TextLine>> for Text<'a> {
    type Output = str;

    fn ref_index(self, range_to_inclusive: RangeToInclusive<TextLine>) -> &'a Self::Output {
        &self.raw[self
            .line_map
            .offset_range_to_inclusive_text_line(range_to_inclusive)]
    }
}

#[test]
pub(crate) fn text_ref_index_by_range_to_inclusive_text_line_works() {
    let t = run_index_test_on_text::<RangeToInclusive<TextLine>>;
    t("hello", ..=(0.into()), "hello");
    t("hello\nworld", ..=(0.into()), "hello\n");
    t("hello\nworld", ..=(1.into()), "hello\nworld");
    t("hello\nworld\n", ..=(2.into()), "hello\nworld\n");
}

// #[test]
// #[should_panic]
// pub(crate) fn text_ref_index_by_range_to_inclusive_text_line_fails() {
//     let t = run_index_test_on_text::<RangeToInclusive<TextLine>>;
//     t("hello\nworld", ..=(2.into()), "hello\nworld");
// }
