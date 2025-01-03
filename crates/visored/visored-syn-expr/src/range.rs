use crate::{
    block::{VdSynBlockArena, VdSynBlockArenaRef, VdSynBlockData, VdSynBlockIdx, VdSynBlockMap},
    clause::{
        VdSynClauseArena, VdSynClauseArenaRef, VdSynClauseData, VdSynClauseEntry, VdSynClauseIdx,
        VdSynClauseMap,
    },
    division::{
        VdSynDivisionArena, VdSynDivisionArenaRef, VdSynDivisionData, VdSynDivisionIdx,
        VdSynDivisionMap,
    },
    expr::{
        VdSynExprArena, VdSynExprArenaRef, VdSynExprData, VdSynExprIdx, VdSynExprMap,
        VdSynLeftDelimiter, VdSynPrefixOpr, VdSynRightDelimiter, VdSynSeparator,
    },
    phrase::{VdSynPhraseArena, VdSynPhraseArenaRef, VdSynPhraseIdx, VdSynPhraseMap},
    sentence::{
        VdSynSentenceArena, VdSynSentenceArenaRef, VdSynSentenceData, VdSynSentenceEnd,
        VdSynSentenceEntry, VdSynSentenceIdx, VdSynSentenceMap,
    },
};
use either::*;
use latex_ast::{ast::math::LxMathCompleteCommandArgument, range::LxAstTokenIdxRangeMap};
use latex_token::idx::{LxMathTokenIdx, LxTokenIdxRange};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynExprTokenIdxRange {
    Standard(LxTokenIdxRange),
}
impl VdSynExprTokenIdxRange {
    fn join(self, other: VdSynExprTokenIdxRange) -> Self {
        match (self, other) {
            (VdSynExprTokenIdxRange::Standard(slf), VdSynExprTokenIdxRange::Standard(other)) => {
                VdSynExprTokenIdxRange::Standard(slf.join(other))
            }
        }
    }
}

pub type VdSynPhraseTokenIdxRange = LxTokenIdxRange;
pub type VdSynClauseTokenIdxRange = LxTokenIdxRange;
pub type VdSynSentenceTokenIdxRange = LxTokenIdxRange;
pub type VdSynBlockTokenIdxRange = LxTokenIdxRange;
pub type VdSynDivisionTokenIdxRange = LxTokenIdxRange;
pub type VdSynExprTokenIdxRangeMap = VdSynExprMap<VdSynExprTokenIdxRange>;
pub type VdSynPhraseTokenIdxRangeMap = VdSynPhraseMap<VdSynPhraseTokenIdxRange>;
pub type VdSynClauseTokenIdxRangeMap = VdSynClauseMap<VdSynClauseTokenIdxRange>;
pub type VdSynSentenceTokenIdxRangeMap = VdSynSentenceMap<VdSynSentenceTokenIdxRange>;
pub type VdSynBlockTokenIdxRangeMap = VdSynBlockMap<VdSynBlockTokenIdxRange>;
pub type VdSynDivisionTokenIdxRangeMap = VdSynDivisionMap<VdSynDivisionTokenIdxRange>;

pub fn calc_expr_range_map(
    lx_ast_range_map: &LxAstTokenIdxRangeMap,
    expr_arena: &VdSynExprArena,
    phrase_arena: &VdSynPhraseArena,
    clause_arena: &VdSynClauseArena,
    sentence_arena: &VdSynSentenceArena,
    stmt_arena: &VdSynBlockArena,
    division_arena: &VdSynDivisionArena,
) -> (
    VdSynExprTokenIdxRangeMap,
    VdSynPhraseTokenIdxRangeMap,
    VdSynClauseTokenIdxRangeMap,
    VdSynSentenceTokenIdxRangeMap,
    VdSynBlockTokenIdxRangeMap,
    VdSynDivisionTokenIdxRangeMap,
) {
    let mut calculator = VdSynExprRangeCalculator::new(
        lx_ast_range_map,
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

struct VdSynExprRangeCalculator<'db> {
    lx_ast_range_map: &'db LxAstTokenIdxRangeMap,
    expr_arena: VdSynExprArenaRef<'db>,
    phrase_arena: VdSynPhraseArenaRef<'db>,
    clause_arena: VdSynClauseArenaRef<'db>,
    sentence_arena: VdSynSentenceArenaRef<'db>,
    stmt_arena: VdSynBlockArenaRef<'db>,
    division_arena: VdSynDivisionArenaRef<'db>,
    expr_range_map: VdSynExprTokenIdxRangeMap,
    phrase_range_map: VdSynPhraseTokenIdxRangeMap,
    clause_range_map: VdSynClauseTokenIdxRangeMap,
    sentence_range_map: VdSynSentenceTokenIdxRangeMap,
    stmt_range_map: VdSynBlockTokenIdxRangeMap,
    division_range_map: VdSynDivisionTokenIdxRangeMap,
}

impl<'db> VdSynExprRangeCalculator<'db> {
    fn new(
        lx_ast_range_map: &'db LxAstTokenIdxRangeMap,
        expr_arena: &'db VdSynExprArena,
        phrase_arena: &'db VdSynPhraseArena,
        clause_arena: &'db VdSynClauseArena,
        sentence_arena: &'db VdSynSentenceArena,
        stmt_arena: &'db VdSynBlockArena,
        division_arena: &'db VdSynDivisionArena,
    ) -> Self {
        Self {
            lx_ast_range_map,
            expr_arena: expr_arena.as_arena_ref(),
            phrase_arena: phrase_arena.as_arena_ref(),
            clause_arena: clause_arena.as_arena_ref(),
            sentence_arena: sentence_arena.as_arena_ref(),
            stmt_arena: stmt_arena.as_arena_ref(),
            division_arena: division_arena.as_arena_ref(),
            expr_range_map: VdSynExprTokenIdxRangeMap::new(expr_arena),
            phrase_range_map: VdSynPhraseTokenIdxRangeMap::new(phrase_arena),
            clause_range_map: VdSynClauseTokenIdxRangeMap::new(clause_arena),
            sentence_range_map: VdSynSentenceTokenIdxRangeMap::new(sentence_arena),
            stmt_range_map: VdSynBlockTokenIdxRangeMap::new(stmt_arena),
            division_range_map: VdSynDivisionTokenIdxRangeMap::new(division_arena),
        }
    }
}

impl<'db> VdSynExprRangeCalculator<'db> {
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
        for division in self.division_arena.index_iter() {
            self.infer_division(division);
        }
    }

    fn infer_expr(&mut self, expr: VdSynExprIdx) {
        if self.expr_range_map.has(expr) {
            return;
        }
        let range = self.calc_expr(expr);
        self.expr_range_map.insert(expr, range);
    }

    fn calc_expr(&mut self, expr: VdSynExprIdx) -> VdSynExprTokenIdxRange {
        let expr_arena = self.expr_arena;
        match expr_arena[expr] {
            VdSynExprData::Literal {
                token_idx_range, ..
            } => VdSynExprTokenIdxRange::Standard(token_idx_range),
            VdSynExprData::Letter {
                token_idx_range, ..
            } => VdSynExprTokenIdxRange::Standard(token_idx_range),
            VdSynExprData::BaseOpr { opr } => todo!(),
            VdSynExprData::Binary { lopd, ropd, .. } => {
                let lopd_range = self.get_expr(lopd);
                let ropd_range = self.get_expr(ropd);
                lopd_range.join(ropd_range)
            }
            VdSynExprData::Prefix { opr, opd } => {
                let opd_range = self.get_expr(opd);
                let opr_range = match opr {
                    VdSynPrefixOpr::Base(lx_token_idx_range, _) => {
                        VdSynExprTokenIdxRange::Standard(lx_token_idx_range)
                    }
                    VdSynPrefixOpr::Composite(expr, _) => self.get_expr(expr),
                };
                opr_range.join(opd_range)
            }
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::Attach { base, ref scripts } => {
                let mut range = self.get_expr(base);
                for &(_, script) in scripts {
                    range = range.join(self.get_expr(script));
                }
                range
            }
            VdSynExprData::UniadicChain => todo!(),
            VdSynExprData::VariadicChain => todo!(),
            VdSynExprData::UniadicArray => todo!(),
            VdSynExprData::VariadicArray => todo!(),
            VdSynExprData::Err(ref e) => VdSynExprTokenIdxRange::Standard(e.token_idx_range()),
            VdSynExprData::SeparatedList {
                items,
                ref separators,
                ..
            } => {
                debug_assert!(items.len() > separators.len());
                // use the first and the last fragment's range
                let first_range =
                    self.get_expr(items.first().expect("fragments are always non-empty"));
                let last_range =
                    self.get_expr(items.last().expect("fragments are always non-empty"));
                first_range.join(last_range)
            }
            VdSynExprData::LxDelimited {
                left_delimiter_token_idx,
                right_delimiter_token_idx,
                ..
            } => VdSynExprTokenIdxRange::Standard(LxTokenIdxRange::new_closed(
                *left_delimiter_token_idx,
                *right_delimiter_token_idx,
            )),
            VdSynExprData::Delimited {
                left_delimiter,

                right_delimiter,
                ..
            } => {
                let left_delimiter_range = match left_delimiter {
                    VdSynLeftDelimiter::Base(token_idx_range, _) => {
                        VdSynExprTokenIdxRange::Standard(token_idx_range)
                    }
                    VdSynLeftDelimiter::Composite(expr, _) => self.get_expr(expr),
                };
                let right_delimiter_range = match right_delimiter {
                    VdSynRightDelimiter::Base(token_idx_range, _) => {
                        VdSynExprTokenIdxRange::Standard(token_idx_range)
                    }
                    VdSynRightDelimiter::Composite(expr, _) => self.get_expr(expr),
                };
                left_delimiter_range.join(right_delimiter_range)
            }
            VdSynExprData::Fraction {
                command_token_idx,
                denominator_arg,
                ..
            } => self.calc_complete_command(command_token_idx, denominator_arg),
            VdSynExprData::Sqrt {
                command_token_idx,
                radicand_arg,
                ..
            } => self.calc_complete_command(command_token_idx, radicand_arg),
        }
    }

    fn calc_complete_command(
        &mut self,
        command_token_idx: LxMathTokenIdx,
        last_arg: LxMathCompleteCommandArgument,
    ) -> VdSynExprTokenIdxRange {
        VdSynExprTokenIdxRange::Standard(match last_arg {
            LxMathCompleteCommandArgument::MathAst(ast) => self.lx_ast_range_map[ast],
            LxMathCompleteCommandArgument::Asts {
                lcurl_token_idx,
                asts,
                rcurl_token_idx,
            } => LxTokenIdxRange::new_closed(*lcurl_token_idx, *rcurl_token_idx),
        })
    }

    fn get_expr(&mut self, expr: VdSynExprIdx) -> VdSynExprTokenIdxRange {
        self.infer_expr(expr);
        self.expr_range_map[expr]
    }

    fn infer_phrase(&mut self, phrase: VdSynPhraseIdx) {
        if self.phrase_range_map.has(phrase) {
            return;
        }
        let range = self.calc_phrase(phrase);
        self.phrase_range_map.insert(phrase, range);
    }

    fn calc_phrase(&mut self, phrase: VdSynPhraseIdx) -> VdSynPhraseTokenIdxRange {
        todo!()
    }

    fn get_phrase(&mut self, phrase: VdSynPhraseIdx) -> VdSynPhraseTokenIdxRange {
        self.infer_phrase(phrase);
        self.phrase_range_map[phrase]
    }

    fn infer_clause(&mut self, clause: VdSynClauseIdx) {
        if self.clause_range_map.has(clause) {
            return;
        }
        let range = self.calc_clause(clause);
        self.clause_range_map.insert(clause, range);
    }

    fn calc_clause(&mut self, clause: VdSynClauseIdx) -> VdSynClauseTokenIdxRange {
        match self.clause_arena[clause] {
            VdSynClauseEntry::Cnl { ref tokens, .. } => {
                let first = tokens
                    .first()
                    .expect("cnl tokens are always non-empty")
                    .lx_ast;
                let last = tokens
                    .last()
                    .expect("cnl tokens are always non-empty")
                    .lx_ast;
                self.lx_ast_range_map[first].join(self.lx_ast_range_map[last])
            }
            VdSynClauseEntry::Unl { tokens, .. } => todo!(),
        }
    }

    fn get_clause(&mut self, clause: VdSynClauseIdx) -> VdSynClauseTokenIdxRange {
        self.infer_clause(clause);
        self.clause_range_map[clause]
    }

    fn infer_sentence(&mut self, sentence: VdSynSentenceIdx) {
        if self.sentence_range_map.has(sentence) {
            return;
        }
        let range = self.calc_sentence(sentence);
        self.sentence_range_map.insert(sentence, range);
    }

    fn calc_sentence(&mut self, sentence: VdSynSentenceIdx) -> VdSynSentenceTokenIdxRange {
        let sentence_entry = &self.sentence_arena[sentence];
        match *sentence_entry.data() {
            VdSynSentenceData::Clauses { clauses, end } => {
                let clauses_range = self.get_clause(clauses.start());
                match end {
                    VdSynSentenceEnd::Period(token_idx) => clauses_range.to_included(*token_idx),
                    VdSynSentenceEnd::Void => clauses_range,
                }
            }
            VdSynSentenceData::Pristine => match sentence_entry {
                VdSynSentenceEntry::Cnl { tokens, .. } => {
                    let first = tokens
                        .first()
                        .expect("cnl tokens are always non-empty")
                        .lx_ast;
                    let last = tokens
                        .last()
                        .expect("cnl tokens are always non-empty")
                        .lx_ast;
                    self.lx_ast_range_map[first].join(self.lx_ast_range_map[last])
                }
                VdSynSentenceEntry::Unl { tokens, .. } => todo!(),
            },
        }
    }

    fn get_sentence(&mut self, sentence: VdSynSentenceIdx) -> VdSynSentenceTokenIdxRange {
        self.infer_sentence(sentence);
        self.sentence_range_map[sentence]
    }

    fn infer_stmt(&mut self, stmt: VdSynBlockIdx) {
        if self.stmt_range_map.has(stmt) {
            return;
        }
        let range = self.calc_stmt(stmt);
        self.stmt_range_map.insert(stmt, range);
    }

    fn calc_stmt(&mut self, stmt: VdSynBlockIdx) -> VdSynBlockTokenIdxRange {
        match self.stmt_arena[stmt] {
            VdSynBlockData::Paragraph(sentences) => {
                let first = self.get_sentence(sentences.start());
                let last =
                    self.get_sentence(sentences.last().expect("sentences are always non-empty"));
                first.join(last)
            }
            VdSynBlockData::Environment {
                begin_command_token_idx,
                end_rcurl_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*begin_command_token_idx, *end_rcurl_token_idx),
        }
    }

    fn get_stmt(&mut self, stmt: VdSynBlockIdx) -> VdSynBlockTokenIdxRange {
        self.infer_stmt(stmt);
        self.stmt_range_map[stmt]
    }

    fn infer_division(&mut self, division: VdSynDivisionIdx) {
        if self.division_range_map.has(division) {
            return;
        }
        let range = self.calc_division(division);
        self.division_range_map.insert(division, range);
    }

    fn calc_division(&mut self, division: VdSynDivisionIdx) -> VdSynDivisionTokenIdxRange {
        match self.division_arena[division] {
            VdSynDivisionData::Stmts { stmts } => {
                // TODO: this might be wrong
                let first = self.get_stmt(stmts.first().expect("stmts are always non-empty"));
                let last = self.get_stmt(stmts.last().expect("stmts are always non-empty"));
                first.join(last)
            }
            VdSynDivisionData::Divisions {
                command_token_idx,
                rcurl_token_idx,
                subdivisions,
                ..
            } => match subdivisions.last() {
                Some(last) => {
                    LxTokenIdxRange::new(*command_token_idx, self.get_division(last).end())
                }
                None => LxTokenIdxRange::new_closed(*command_token_idx, *rcurl_token_idx),
            },
        }
    }

    fn get_division(&mut self, division: VdSynDivisionIdx) -> VdSynDivisionTokenIdxRange {
        self.infer_division(division);
        self.division_range_map[division]
    }

    fn finish(
        self,
    ) -> (
        VdSynExprTokenIdxRangeMap,
        VdSynPhraseTokenIdxRangeMap,
        VdSynClauseTokenIdxRangeMap,
        VdSynSentenceTokenIdxRangeMap,
        VdSynBlockTokenIdxRangeMap,
        VdSynDivisionTokenIdxRangeMap,
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
