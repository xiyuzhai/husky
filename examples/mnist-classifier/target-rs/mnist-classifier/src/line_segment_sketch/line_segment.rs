use super::*;
#[rustfmt::skip]
#[allow(non_upper_case_globals)]
pub static mut __LineSegment__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

#[rustfmt::skip]
#[ad_hoc_devsoul_dependency::value_conversion]
#[derive(Debug, Clone, PartialEq)]
pub struct LineSegment {
    pub start: crate::geom2d::Point2d,
    pub end: crate::geom2d::Point2d,
}

impl LineSegment {
    pub fn __constructor(start: crate::geom2d::Point2d, end: crate::geom2d::Point2d) -> Self {
        Self{
            start,
            end,
        }
    }
}

#[rustfmt::skip]
impl crate::line_segment_sketch::line_segment::LineSegment {
    pub fn displacement(&self) -> crate::geom2d::Vector2d {
        self.start.to(&self.end)
    }

    pub fn dist_to_point(&self, pt: &crate::geom2d::Point2d) -> f32 {
        let ab = self.displacement();
        let ap = self.start.to(pt);
        if ab.dot(&ap) < 0.0f32 {
            ap.norm()
        } else {
            let bp = self.end.to(pt);
            if ab.dot(&bp) > 0.0f32 {
                bp.norm()
            } else {
                ab.cross(&ap).abs() / ab.norm()
            }
        }
    }
}
#[rustfmt::skip]
#[allow(non_upper_case_globals)]
pub static mut __LineSegment__displacement__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;


#[rustfmt::skip]
#[allow(non_upper_case_globals)]
pub static mut __LineSegment__dist_to_point__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

