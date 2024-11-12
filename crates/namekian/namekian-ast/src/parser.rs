use crate::{
    data::{NamAstArena, NamAstIdxRange},
    level::NamAstLevel,
    paragraph::{NamParagraph, NamParagraphIter},
};
use std::iter::Peekable;

pub struct NamParser<'a> {
    input: &'a str,
    paragraph_iter: Peekable<NamParagraphIter<'a>>,
    level: NamAstLevel,
    arena: NamAstArena,
}

impl<'a> NamParser<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            input,
            paragraph_iter: NamParagraphIter::new(input).peekable(),
            level: NamAstLevel::Book,
            arena: Default::default(),
        }
    }

    pub(crate) fn with_level<R>(&mut self, level: NamAstLevel, f: impl Fn(&mut Self) -> R) -> R {
        let prev_level = std::mem::replace(&mut self.level, level);
        let r = f(self);
        self.level = prev_level;
        r
    }

    pub(crate) fn next_paragraph_within_current_level(&mut self) -> Option<NamParagraph<'a>> {
        let paragraph = self.paragraph_iter.peek()?;
        if paragraph.lead.level() <= self.level {
            return None;
        }
        self.paragraph_iter.next()
    }

    pub(crate) fn alloc_asts(&mut self, asts: Vec<crate::data::NamAstData>) -> NamAstIdxRange {
        self.arena.alloc_batch(asts)
    }

    pub(crate) fn finish(self) -> NamAstArena {
        self.arena
    }
}
