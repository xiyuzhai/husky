#![feature(closure_track_caller)]
pub mod helpers;
pub mod jar;
mod line_map;
#[cfg(test)]
mod tests;

use self::jar::*;
#[cfg(test)]
use self::tests::*;
use husky_text_protocol::{line_map::*, offset::TextOffsetRange, position::TextLine, range::*};
use husky_vfs::path::module_path::ModulePath;
use line_map::module_text_line_map;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Text<'a> {
    raw: &'a str,
    line_map: &'a LineMap,
}

impl<'a> Text<'a> {
    pub fn indexed_lines(self) -> impl Iterator<Item = (TextLine, &'a str)> {
        self.line_map
            .all_text_line_range()
            .map(move |text_line| (text_line, self.text_within(text_line)))
    }

    pub fn raw(&self) -> &'a str {
        self.raw
    }
}

pub trait HasText: Copy {
    fn text<'a>(self, db: &'a ::salsa::Db) -> Text<'a>;
}

impl HasText for ModulePath {
    fn text<'a>(self, db: &'a ::salsa::Db) -> Text<'a> {
        Text {
            raw: self.raw_text(db),
            line_map: module_text_line_map(db, self),
        }
    }
}

impl<'a> std::fmt::Debug for Text<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Text...")
    }
}

impl<'a> Text<'a> {
    pub fn offset_range(self, range: TextPositionRange) -> TextOffsetRange {
        self.line_map.offset_range(range)
    }
}

mod index;
