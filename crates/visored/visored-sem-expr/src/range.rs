use crate::{
    clause::{
        VdSemClauseArena, VdSemClauseArenaRef, VdSemClauseData, VdSemClauseIdx, VdSemClauseMap,
    },
    division::{VdSemDivisionArena, VdSemDivisionMap},
    expr::{
        VdSemExprArena, VdSemExprArenaRef, VdSemExprData, VdSemExprIdx, VdSemExprMap,
        VdSemLeftDelimiter, VdSemPrefixOpr, VdSemRightDelimiter, VdSemSeparator,
    },
    phrase::{VdSemPhraseArena, VdSemPhraseArenaRef, VdSemPhraseIdx, VdSemPhraseMap},
    sentence::{
        VdSemSentenceArena, VdSemSentenceArenaRef, VdSemSentenceData, VdSemSentenceEnd,
        VdSemSentenceIdx, VdSemSentenceMap,
    },
    stmt::{VdSemStmtArena, VdSemStmtArenaRef, VdSemStmtData, VdSemStmtIdx, VdSemStmtMap},
};
use either::*;
use latex_token::idx::LxTokenIdxRange;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSemExprTokenIdxRange {
    Standard(LxTokenIdxRange),
}
impl VdSemExprTokenIdxRange {
    fn join(self, other: VdSemExprTokenIdxRange) -> Self {
        match (self, other) {
            (VdSemExprTokenIdxRange::Standard(slf), VdSemExprTokenIdxRange::Standard(other)) => {
                VdSemExprTokenIdxRange::Standard(slf.join(other))
            }
        }
    }
}

pub type VdSemPhraseTokenIdxRange = LxTokenIdxRange;
pub type VdSemClauseTokenIdxRange = LxTokenIdxRange;
pub type VdSemSentenceTokenIdxRange = LxTokenIdxRange;
pub type VdSemStmtTokenIdxRange = LxTokenIdxRange;
pub type VdSemDivisionTokenIdxRange = LxTokenIdxRange;
pub type VdSemExprTokenIdxRangeMap = VdSemExprMap<VdSemExprTokenIdxRange>;
pub type VdSemPhraseTokenIdxRangeMap = VdSemPhraseMap<VdSemPhraseTokenIdxRange>;
pub type VdSemClauseTokenIdxRangeMap = VdSemClauseMap<VdSemClauseTokenIdxRange>;
pub type VdSemSentenceTokenIdxRangeMap = VdSemSentenceMap<VdSemSentenceTokenIdxRange>;
pub type VdSemStmtTokenIdxRangeMap = VdSemStmtMap<VdSemStmtTokenIdxRange>;
pub type VdSemDivisionTokenIdxRangeMap = VdSemDivisionMap<VdSemDivisionTokenIdxRange>;

pub fn calc_expr_range_map(
    db: &::salsa::Db,
    expr_arena: &VdSemExprArena,
    phrase_arena: &VdSemPhraseArena,
    clause_arena: &VdSemClauseArena,
    sentence_arena: &VdSemSentenceArena,
    stmt_arena: &VdSemStmtArena,
    division_arena: &VdSemDivisionArena,
) -> (
    VdSemExprTokenIdxRangeMap,
    VdSemPhraseTokenIdxRangeMap,
    VdSemClauseTokenIdxRangeMap,
    VdSemSentenceTokenIdxRangeMap,
    VdSemStmtTokenIdxRangeMap,
    VdSemDivisionTokenIdxRangeMap,
) {
    let mut calculator = VdSemExprRangeCalculator::new(
        db,
        expr_arena,
        phrase_arena,
        clause_arena,
        sentence_arena,
        stmt_arena,
        division_arena,
    );
    calculator.infer_all_ranges();
    calculator.finish()
}

struct VdSemExprRangeCalculator<'db> {
    db: &'db ::salsa::Db,
    expr_arena: VdSemExprArenaRef<'db>,
    phrase_arena: VdSemPhraseArenaRef<'db>,
    clause_arena: VdSemClauseArenaRef<'db>,
    sentence_arena: VdSemSentenceArenaRef<'db>,
    stmt_arena: VdSemStmtArenaRef<'db>,
    expr_range_map: VdSemExprTokenIdxRangeMap,
    phrase_range_map: VdSemPhraseTokenIdxRangeMap,
    clause_range_map: VdSemClauseTokenIdxRangeMap,
    sentence_range_map: VdSemSentenceTokenIdxRangeMap,
    stmt_range_map: VdSemStmtTokenIdxRangeMap,
    division_range_map: VdSemDivisionTokenIdxRangeMap,
}

impl<'db> VdSemExprRangeCalculator<'db> {
    fn new(
        db: &'db ::salsa::Db,
        expr_arena: &'db VdSemExprArena,
        phrase_arena: &'db VdSemPhraseArena,
        clause_arena: &'db VdSemClauseArena,
        sentence_arena: &'db VdSemSentenceArena,
        stmt_arena: &'db VdSemStmtArena,
        division_arena: &'db VdSemDivisionArena,
    ) -> Self {
        Self {
            db,
            expr_arena: expr_arena.as_arena_ref(),
            phrase_arena: phrase_arena.as_arena_ref(),
            clause_arena: clause_arena.as_arena_ref(),
            sentence_arena: sentence_arena.as_arena_ref(),
            stmt_arena: stmt_arena.as_arena_ref(),
            expr_range_map: VdSemExprTokenIdxRangeMap::new(expr_arena),
            phrase_range_map: VdSemPhraseTokenIdxRangeMap::new(phrase_arena),
            clause_range_map: VdSemClauseTokenIdxRangeMap::new(clause_arena),
            sentence_range_map: VdSemSentenceTokenIdxRangeMap::new(sentence_arena),
            stmt_range_map: VdSemStmtTokenIdxRangeMap::new(stmt_arena),
            division_range_map: VdSemDivisionTokenIdxRangeMap::new(division_arena),
        }
    }
}

impl<'db> VdSemExprRangeCalculator<'db> {
    fn infer_all_ranges(&mut self) {
        for expr in self.expr_arena.index_iter() {
            self.infer_expr(expr);
        }
        for phrase in self.phrase_arena.index_iter() {
            self.infer_phrase(phrase);
        }
        for clause in self.clause_arena.index_iter() {
            self.infer_clause(clause);
        }
        for sentence in self.sentence_arena.index_iter() {
            self.infer_sentence(sentence);
        }
        for stmt in self.stmt_arena.index_iter() {
            self.infer_stmt(stmt);
        }
    }

    fn infer_expr(&mut self, expr: VdSemExprIdx) {
        if self.expr_range_map.has(expr) {
            return;
        }
        let range = self.calc_expr(expr);
        self.expr_range_map.insert(expr, range);
    }

    fn calc_expr(&mut self, expr: VdSemExprIdx) -> VdSemExprTokenIdxRange {
        let expr_arena = self.expr_arena;
        match expr_arena[expr] {
            VdSemExprData::Literal {
                token_idx_range, ..
            } => VdSemExprTokenIdxRange::Standard(token_idx_range),
            VdSemExprData::Letter {
                token_idx_range, ..
            } => VdSemExprTokenIdxRange::Standard(token_idx_range),
            VdSemExprData::BaseOpr { opr } => todo!(),
            VdSemExprData::Binary { lopd, ropd, .. } => {
                let lopd_range = self.get_expr(lopd);
                let ropd_range = self.get_expr(ropd);
                lopd_range.join(ropd_range)
            }
            VdSemExprData::Prefix { opr, opd, .. } => {
                let opd_range = self.get_expr(opd);
                let opr_range = match opr {
                    VdSemPrefixOpr::Base(lx_token_idx_range, _) => {
                        VdSemExprTokenIdxRange::Standard(lx_token_idx_range)
                    }
                    VdSemPrefixOpr::Composite(expr, _) => self.get_expr(expr),
                };
                opr_range.join(opd_range)
            }
            VdSemExprData::Suffix { opd, opr, .. } => todo!(),
            VdSemExprData::Attach {
                base, ref scripts, ..
            } => {
                let mut range = self.get_expr(base);
                for &(_, script) in scripts {
                    range = range.join(self.get_expr(script));
                }
                range
            }
            VdSemExprData::UniadicChain => todo!(),
            VdSemExprData::VariadicChain => todo!(),
            VdSemExprData::UniadicArray => todo!(),
            VdSemExprData::VariadicArray => todo!(),
            VdSemExprData::SeparatedList { items, .. } => {
                let first_range = self.get_expr(items.start());
                let last_range = self.get_expr(items.last().expect("items are always non-empty"));
                first_range.join(last_range)
            }
            VdSemExprData::LxDelimited {
                left_delimiter_token_idx,
                right_delimiter_token_idx,
                ..
            } => VdSemExprTokenIdxRange::Standard(LxTokenIdxRange::new_closed(
                *left_delimiter_token_idx,
                *right_delimiter_token_idx,
            )),
            VdSemExprData::Delimited {
                left_delimiter,

                right_delimiter,
                ..
            } => {
                let left_delimiter_range = match left_delimiter {
                    VdSemLeftDelimiter::Base(token_idx_range, _) => {
                        VdSemExprTokenIdxRange::Standard(token_idx_range)
                    }
                    VdSemLeftDelimiter::Composite(expr, _) => self.get_expr(expr),
                };
                let right_delimiter_range = match right_delimiter {
                    VdSemRightDelimiter::Base(token_idx_range, _) => {
                        VdSemExprTokenIdxRange::Standard(token_idx_range)
                    }
                    VdSemRightDelimiter::Composite(expr, _) => self.get_expr(expr),
                };
                left_delimiter_range.join(right_delimiter_range)
            }
            VdSemExprData::Fraction {
                command_token_idx,
                denominator_rcurl_token_idx,
                ..
            } => VdSemExprTokenIdxRange::Standard(LxTokenIdxRange::new_closed(
                *command_token_idx,
                *denominator_rcurl_token_idx,
            )),
            VdSemExprData::Sqrt {
                command_token_idx,
                radicand_rcurl_token_idx,
                ..
            } => VdSemExprTokenIdxRange::Standard(LxTokenIdxRange::new_closed(
                *command_token_idx,
                *radicand_rcurl_token_idx,
            )),
        }
    }

    fn get_expr(&mut self, expr: VdSemExprIdx) -> VdSemExprTokenIdxRange {
        self.infer_expr(expr);
        self.expr_range_map[expr]
    }

    fn infer_phrase(&mut self, phrase: VdSemPhraseIdx) {
        if self.phrase_range_map.has(phrase) {
            return;
        }
        let range = self.calc_phrase(phrase);
        self.phrase_range_map.insert(phrase, range);
    }

    fn calc_phrase(&mut self, phrase: VdSemPhraseIdx) -> VdSemPhraseTokenIdxRange {
        todo!()
    }

    fn get_phrase(&mut self, phrase: VdSemPhraseIdx) -> VdSemPhraseTokenIdxRange {
        self.infer_phrase(phrase);
        self.phrase_range_map[phrase]
    }

    fn infer_clause(&mut self, clause: VdSemClauseIdx) {
        if self.clause_range_map.has(clause) {
            return;
        }
        let range = self.calc_clause(clause);
        self.clause_range_map.insert(clause, range);
    }

    fn calc_clause(&mut self, clause: VdSemClauseIdx) -> VdSemClauseTokenIdxRange {
        match self.clause_arena[clause] {
            VdSemClauseData::Let {
                let_token_idx,
                right_dollar_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*let_token_idx, *right_dollar_token_idx),
            VdSemClauseData::Assume {
                assume_token_idx,
                right_dollar_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*assume_token_idx, *right_dollar_token_idx),
            VdSemClauseData::Then {
                then_token_idx,
                right_dollar_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*then_token_idx, *right_dollar_token_idx),
            VdSemClauseData::Verb => todo!(),
        }
    }

    fn get_clause(&mut self, clause: VdSemClauseIdx) -> VdSemClauseTokenIdxRange {
        self.infer_clause(clause);
        self.clause_range_map[clause]
    }

    fn infer_sentence(&mut self, sentence: VdSemSentenceIdx) {
        if self.sentence_range_map.has(sentence) {
            return;
        }
        let range = self.calc_sentence(sentence);
        self.sentence_range_map.insert(sentence, range);
    }

    fn calc_sentence(&mut self, sentence: VdSemSentenceIdx) -> VdSemSentenceTokenIdxRange {
        match self.sentence_arena[sentence] {
            VdSemSentenceData::Clauses { clauses, end } => {
                let clauses_range = self.get_clause(clauses.start());
                match end {
                    VdSemSentenceEnd::Period(token_idx) => clauses_range.to_included(*token_idx),
                }
            }
        }
    }

    fn get_sentence(&mut self, sentence: VdSemSentenceIdx) -> VdSemSentenceTokenIdxRange {
        self.infer_sentence(sentence);
        self.sentence_range_map[sentence]
    }

    fn infer_stmt(&mut self, stmt: VdSemStmtIdx) {
        if self.stmt_range_map.has(stmt) {
            return;
        }
        let range = self.calc_stmt(stmt);
        self.stmt_range_map.insert(stmt, range);
    }

    fn calc_stmt(&mut self, stmt: VdSemStmtIdx) -> VdSemStmtTokenIdxRange {
        match self.stmt_arena[stmt] {
            VdSemStmtData::Paragraph(sentences) => {
                let first = self.get_sentence(sentences.start());
                let last =
                    self.get_sentence(sentences.last().expect("sentences are always non-empty"));
                first.join(last)
            }
            VdSemStmtData::Block { environment, stmts } => todo!(),
        }
    }

    fn get_stmt(&mut self, stmt: VdSemStmtIdx) -> VdSemStmtTokenIdxRange {
        self.infer_stmt(stmt);
        self.stmt_range_map[stmt]
    }

    fn finish(
        self,
    ) -> (
        VdSemExprTokenIdxRangeMap,
        VdSemPhraseTokenIdxRangeMap,
        VdSemClauseTokenIdxRangeMap,
        VdSemSentenceTokenIdxRangeMap,
        VdSemStmtTokenIdxRangeMap,
        VdSemDivisionTokenIdxRangeMap,
    ) {
        (
            self.expr_range_map,
            self.phrase_range_map,
            self.clause_range_map,
            self.sentence_range_map,
            self.stmt_range_map,
            self.division_range_map,
        )
    }
}
