use crate::{
    clause::{VdSemClauseArena, VdSemClauseData, VdSemClauseIdx},
    expr::{VdSemExprArena, VdSemExprData, VdSemExprIdx},
    helpers::latex_fmt::VdSemExprLaTeXFormatter,
    phrase::{VdSemPhraseArena, VdSemPhraseData, VdSemPhraseIdx},
    region::VdSemExprRegionData,
    sentence::{VdSemSentenceArena, VdSemSentenceData, VdSemSentenceIdx},
};

use super::{division::VdSemDivisionArena, stmt::VdSemStmtArena};

pub struct VdSemExprTestBuilder<'db> {
    db: &'db ::salsa::Db,
    expr_arena: VdSemExprArena,
    phrase_arena: VdSemPhraseArena,
    clause_arena: VdSemClauseArena,
    sentence_arena: VdSemSentenceArena,
    stmt_arena: VdSemStmtArena,
    division_arena: VdSemDivisionArena,
}

impl<'db> VdSemExprTestBuilder<'db> {
    pub fn new(db: &'db ::salsa::Db) -> Self {
        Self {
            db,
            expr_arena: VdSemExprArena::default(),
            phrase_arena: VdSemPhraseArena::default(),
            clause_arena: VdSemClauseArena::default(),
            sentence_arena: VdSemSentenceArena::default(),
            stmt_arena: VdSemStmtArena::default(),
            division_arena: VdSemDivisionArena::default(),
        }
    }
}

impl<'db> VdSemExprTestBuilder<'db> {
    pub fn latex_formatter<'a>(&'a self) -> VdSemExprLaTeXFormatter<'a> {
        VdSemExprLaTeXFormatter::new(
            self.db,
            self.expr_arena.as_arena_ref(),
            self.phrase_arena.as_arena_ref(),
            self.clause_arena.as_arena_ref(),
            self.sentence_arena.as_arena_ref(),
        )
    }
}

impl<'db> VdSemExprTestBuilder<'db> {
    #[track_caller]
    pub fn new_expr_checked(&mut self, data: VdSemExprData, expected: &str) -> VdSemExprIdx {
        let expr = self.expr_arena.alloc_one(data);
        let mut formatter = self.latex_formatter();
        formatter.fmt_expr(expr);
        assert_eq!(&formatter.finish(), expected);
        expr
    }

    #[track_caller]
    pub fn new_phrase_checked(&mut self, data: VdSemPhraseData, expected: &str) -> VdSemPhraseIdx {
        let phrase = self.phrase_arena.alloc_one(data);
        let mut formatter = self.latex_formatter();
        formatter.fmt_phrase(phrase);
        assert_eq!(&formatter.finish(), expected);
        phrase
    }

    #[track_caller]
    pub fn new_clause_checked(&mut self, data: VdSemClauseData, expected: &str) -> VdSemClauseIdx {
        let clause = self.clause_arena.alloc_one(data);
        let mut formatter = self.latex_formatter();
        formatter.fmt_clause(clause);
        assert_eq!(&formatter.finish(), expected);
        clause
    }

    #[track_caller]
    pub fn new_sentence_checked(
        &mut self,
        data: VdSemSentenceData,
        expected: &str,
    ) -> VdSemSentenceIdx {
        let sentence = self.sentence_arena.alloc_one(data);
        let mut formatter = self.latex_formatter();
        formatter.fmt_sentence(sentence);
        assert_eq!(&formatter.finish(), expected);
        sentence
    }

    pub fn finish(self) -> VdSemExprRegionData {
        VdSemExprRegionData::new(
            self.expr_arena,
            self.phrase_arena,
            self.clause_arena,
            self.sentence_arena,
            self.stmt_arena,
            self.division_arena,
        )
    }
}
