use crate::{
    verse::{idx::TokenVerseIdx, iter::TokenVerseIter, start::TokenVerseStart, TokenVerses},
    TokenIdx, TokenIdxRange, TokenJar, TokenStreamState,
};
use husky_text_protocol::{position::TextPosition, range::TextPositionRange};
use husky_token_data::TokenData;
use husky_vfs::path::module_path::ModulePath;

impl std::ops::Index<TokenIdx> for TokenSheetData {
    type Output = TokenData;

    fn index(&self, idx: TokenIdx) -> &Self::Output {
        &self.tokens[idx.index()]
    }
}

pub enum TokenIdxRangeConfig {
    IncludeBoundary,
    ExcludeBoundary,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RangedTokenSheet {
    token_sheet: TokenSheet,
    // external
    token_ranges: Vec<TextPositionRange>,
    comments: Vec<Comment>,
}

#[salsa::tracked(db = TokenDb, jar = TokenJar)]
pub struct TokenSheet {
    #[return_ref]
    pub(crate) data: TokenSheetData,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TokenSheetData {
    tokens: Vec<TokenData>,
    token_verses: TokenVerses,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Comment {
    kind: CommentKind,
    number_of_preceding_tokens: usize,
    range: TextPositionRange,
}

impl Comment {
    pub(crate) fn new(
        kind: CommentKind,
        number_of_preceding_tokens: usize,
        range: TextPositionRange,
    ) -> Self {
        Self {
            kind,
            number_of_preceding_tokens,
            range,
        }
    }

    pub fn number_of_preceding_tokens(&self) -> usize {
        self.number_of_preceding_tokens
    }

    pub fn range(&self) -> TextPositionRange {
        self.range
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CommentKind {
    Todo,
}

impl RangedTokenSheet {
    pub fn len(&self) -> usize {
        self.token_ranges.len()
    }

    pub fn tokens<'a>(&self, db: &'a ::salsa::Db) -> &'a [TokenData] {
        &self.token_sheet.data(db).tokens
    }

    pub fn ranged_token_iter<'a>(
        &'a self,
        db: &'a ::salsa::Db,
    ) -> impl Iterator<Item = (&'a TextPositionRange, &'a TokenData)> + 'a {
        let tokens = self.tokens(db);
        (0..tokens.len())
            .into_iter()
            .map(|i| (&self.token_ranges[i], &tokens[i]))
    }

    pub fn indexed_ranged_token_iter<'a>(
        &'a self,
        db: &'a ::salsa::Db,
    ) -> impl Iterator<Item = (TokenIdx, &'a TextPositionRange, &'a TokenData)> + 'a {
        let tokens = self.tokens(db);
        (0..tokens.len())
            .into_iter()
            .map(|i| (TokenIdx::from_index(i), &self.token_ranges[i], &tokens[i]))
    }

    pub fn token_index_iter<'a>(&'a self) -> impl Iterator<Item = TokenIdx> + 'a {
        (0..self.token_ranges.len())
            .into_iter()
            .map(|i| TokenIdx::from_index(i))
    }

    pub fn search_token_by_position(&self, pos: TextPosition) -> Option<TokenIdx> {
        let index = match self
            .token_ranges
            .binary_search_by(|range1| range1.start.cmp(&pos))
        {
            Ok(i) => i,
            Err(e) => (e > 0).then(|| e - 1)?,
        };
        (self.token_ranges[index].end > pos).then(|| TokenIdx::from_index(index))
    }

    pub fn token_sheet_data<'a>(&self, db: &'a ::salsa::Db) -> &'a TokenSheetData {
        self.token_sheet.data(db)
    }

    pub fn token_text_ranges(&self) -> &[TextPositionRange] {
        self.token_ranges.as_ref()
    }

    pub(crate) fn token_sheet(&self) -> TokenSheet {
        self.token_sheet
    }

    pub fn comments(&self) -> &[Comment] {
        self.comments.as_ref()
    }
}

#[salsa::tracked(jar = TokenJar, return_ref)]
pub(crate) fn ranged_token_sheet(db: &::salsa::Db, module_path: ModulePath) -> RangedTokenSheet {
    crate::lex::lex_tracked(db, module_path.raw_text(db))
}

#[salsa::tracked(jar = TokenJar)]
pub(crate) fn token_sheet(db: &::salsa::Db, module_path: ModulePath) -> TokenSheet {
    ranged_token_sheet(db, module_path).token_sheet
}

impl RangedTokenSheet {
    pub fn new(
        db: &::salsa::Db,
        tokens: Vec<TokenData>,
        token_ranges: Vec<TextPositionRange>,
        comments: Vec<Comment>,
    ) -> RangedTokenSheet {
        let token_verses = TokenVerses::new(&tokens, &token_ranges);
        RangedTokenSheet {
            token_sheet: TokenSheet::new(
                db,
                TokenSheetData {
                    token_verses,
                    tokens,
                },
            ),
            token_ranges,
            comments,
        }
    }

    pub fn token_text_range(&self, token_idx: TokenIdx) -> TextPositionRange {
        debug_assert!(token_idx.index() < self.token_ranges.len());
        self.token_ranges[token_idx.index()]
    }

    pub fn tokens_text_range(&self, token_idx_range: TokenIdxRange) -> TextPositionRange {
        debug_assert!(token_idx_range.end().token_idx() > token_idx_range.start().token_idx());
        let text_range_start = self.token_ranges[token_idx_range.start().index()].start;
        let text_range_end = self.token_ranges[(token_idx_range.end().index() - 1) as usize].end;
        (text_range_start..text_range_end).into()
    }

    pub fn token_stream_state_text_range(
        &self,
        token_stream_state: TokenStreamState,
    ) -> TextPositionRange {
        match token_stream_state.drained() {
            true => {
                let next_token_idx_index = token_stream_state.next_token_idx().index();
                match next_token_idx_index {
                    0 => TextPositionRange::default(),
                    _ => self.token_ranges[(next_token_idx_index - 1) as usize].right_after(),
                }
            }
            false => self.token_ranges[token_stream_state.next_token_idx().index()],
        }
    }
}

impl TokenSheetData {
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    pub fn main_token_verse_iter<'a>(&'a self) -> TokenVerseIter<'a> {
        self.token_verses.main_token_verse_iter(&self.tokens)
    }

    pub fn token_verse_start(&self, token_verse_idx: TokenVerseIdx) -> TokenVerseStart {
        self.token_verses[token_verse_idx].start()
    }

    pub fn token_verse_token_idx_range(&self, token_verse_idx: TokenVerseIdx) -> TokenIdxRange {
        self.token_verses
            .token_verse_token_idx_range(token_verse_idx, self.tokens.len())
    }

    pub fn tokens(&self) -> &[TokenData] {
        self.tokens.as_ref()
    }

    pub fn token_verse_idx(&self, token_idx: TokenIdx) -> TokenVerseIdx {
        self.token_verses.token_verse_idx(token_idx)
    }

    pub fn token_verses(&self) -> &TokenVerses {
        &self.token_verses
    }
}

impl std::ops::Index<TokenVerseIdx> for TokenSheetData {
    type Output = [TokenData];

    fn index(&self, idx: TokenVerseIdx) -> &Self::Output {
        let start = self.token_verses[idx].start().index();
        let end = self
            .token_verses
            .get(idx.next())
            .map(|end| end.start().index())
            .unwrap_or(self.tokens.len());
        &self.tokens[start..end]
    }
}

impl std::ops::Index<TokenIdxRange> for TokenSheetData {
    type Output = [TokenData];

    fn index(&self, token_idx_range: TokenIdxRange) -> &Self::Output {
        let start = token_idx_range.start().index();
        let end = token_idx_range.end().index();
        &self.tokens[start..end]
    }
}
