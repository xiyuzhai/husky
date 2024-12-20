mod parse_iter;
mod title;
mod visitor;

pub use self::parse_iter::*;
pub use self::title::*;
pub use self::visitor::*;

use crate::*;
use husky_coword::BaseCoword;
use idx_arena::{Arena, ArenaIdx};
use smallvec::SmallVec;
use vec_like::{AsVecMapEntry, VecMap};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TomlSectionSheet {
    arena: TomlSectionArena,
    errors: Vec<TomlAstError>,
}

impl std::ops::Deref for TomlSectionSheet {
    type Target = TomlSectionArena;

    fn deref(&self) -> &Self::Target {
        &self.arena
    }
}

pub type TomlSectionArena = Arena<TomlSection>;
pub type TomlSectionIdx = ArenaIdx<TomlSection>;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TomlSection {
    title: TomlSectionTitle,
    kind: TomlSectionKind,
    entries: VecMap<TomlSectionEntry>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TomlSectionEntry {
    line_group_idx: TomlLineGroupIdx,
    key: BaseCoword,
    value: Option<TomlExprIdx>,
}

impl AsVecMapEntry for TomlSectionEntry {
    type K = BaseCoword;

    fn key(&self) -> Self::K
    where
        Self::K: Copy,
    {
        self.key
    }

    fn key_ref(&self) -> &Self::K {
        &self.key
    }
}

impl TomlSectionEntry {
    pub fn line_group_idx(&self) -> TomlLineGroupIdx {
        self.line_group_idx
    }

    pub fn key(&self) -> BaseCoword {
        self.key
    }

    pub fn value(&self) -> Option<TomlExprIdx> {
        self.value
    }
}

impl TomlAst for TomlSectionEntry {
    type Visitor<'a> = TomlSectionEntryVisitor<'a>;
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TomlSectionKind {
    Normal,
    Scattered,
}

impl TomlSection {
    pub fn kind(&self) -> TomlSectionKind {
        self.kind
    }

    pub fn title(&self) -> &TomlSectionTitle {
        &self.title
    }

    pub fn entries(&self) -> &[TomlSectionEntry] {
        &self.entries
    }

    pub fn get_entry(&self, key: BaseCoword) -> Option<&TomlSectionEntry> {
        self.entries.get_entry(key)
    }
}

impl TomlSectionSheet {
    pub(crate) fn parse_collect(
        db: &::salsa::Db,
        toml_token_text: &TomlTokenSheet,
        line_groups: &[TomlLineGroup],
    ) -> Self {
        let mut errors = vec![];
        Self {
            arena: TomlSectionParseIter::new(db, toml_token_text, line_groups, &mut errors)
                .collect(),
            errors,
        }
    }

    pub fn errors(&self) -> &[TomlAstError] {
        &self.errors
    }

    pub fn indexed_section_iter(&self) -> impl Iterator<Item = (TomlSectionIdx, &TomlSection)> {
        self.arena.indexed_iter()
    }
}
