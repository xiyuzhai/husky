use super::*;
use crate::{
    clause::{VdSemClauseArenaRef, VdSemClauseChild, VdSemClauseData, VdSemClauseIdx},
    division::{
        helpers::VdSemDivisionChild, VdSemDivisionArenaRef, VdSemDivisionData, VdSemDivisionIdx,
        VdSemDivisionIdxRange,
    },
    expr::{VdSemExprArenaRef, VdSemExprData, VdSemExprIdx},
    phrase::VdSemPhraseArenaRef,
    range::{
        VdSemClauseTokenIdxRangeMap, VdSemDivisionTokenIdxRangeMap, VdSemExprTokenIdxRange,
        VdSemExprTokenIdxRangeMap, VdSemPhraseTokenIdxRangeMap, VdSemSentenceTokenIdxRangeMap,
        VdSemStmtTokenIdxRangeMap,
    },
    sentence::{VdSemSentenceArenaRef, VdSemSentenceChild, VdSemSentenceData, VdSemSentenceIdx},
    stmt::{VdSemStmtArenaRef, VdSemStmtChild, VdSemStmtData, VdSemStmtIdx, VdSemStmtIdxRange},
};
use husky_tree_utils::display::DisplayTree;
use latex_ast::{ast::LxAstArenaRef, range::LxAstTokenIdxRangeMap};
use latex_token::storage::LxTokenStorage;

pub struct VdSemExprDisplayTreeBuilder<'a> {
    input: &'a str,
    token_storage: &'a LxTokenStorage,
    ast_arena: LxAstArenaRef<'a>,
    ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
    expr_arena: VdSemExprArenaRef<'a>,
    phrase_arena: VdSemPhraseArenaRef<'a>,
    clause_arena: VdSemClauseArenaRef<'a>,
    sentence_arena: VdSemSentenceArenaRef<'a>,
    stmt_arena: VdSemStmtArenaRef<'a>,
    division_arena: VdSemDivisionArenaRef<'a>,
    expr_range_map: &'a VdSemExprTokenIdxRangeMap,
    phrase_range_map: &'a VdSemPhraseTokenIdxRangeMap,
    clause_range_map: &'a VdSemClauseTokenIdxRangeMap,
    sentence_range_map: &'a VdSemSentenceTokenIdxRangeMap,
    stmt_range_map: &'a VdSemStmtTokenIdxRangeMap,
    division_range_map: &'a VdSemDivisionTokenIdxRangeMap,
}
impl<'a> VdSemExprDisplayTreeBuilder<'a> {
    pub(crate) fn new(
        input: &'a str,
        token_storage: &'a LxTokenStorage,
        ast_arena: LxAstArenaRef<'a>,
        ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
        expr_arena: VdSemExprArenaRef<'a>,
        phrase_arena: VdSemPhraseArenaRef<'a>,
        clause_arena: VdSemClauseArenaRef<'a>,
        sentence_arena: VdSemSentenceArenaRef<'a>,
        stmt_arena: VdSemStmtArenaRef<'a>,
        division_arena: VdSemDivisionArenaRef<'a>,
        expr_range_map: &'a VdSemExprTokenIdxRangeMap,
        phrase_range_map: &'a VdSemPhraseTokenIdxRangeMap,
        clause_range_map: &'a VdSemClauseTokenIdxRangeMap,
        sentence_range_map: &'a VdSemSentenceTokenIdxRangeMap,
        stmt_range_map: &'a VdSemStmtTokenIdxRangeMap,
        division_range_map: &'a VdSemDivisionTokenIdxRangeMap,
    ) -> Self {
        Self {
            input,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            expr_arena,
            phrase_arena,
            clause_arena,
            sentence_arena,
            stmt_arena,
            division_arena,
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
        }
    }
}

impl<'a> VdSemExprDisplayTreeBuilder<'a> {
    pub fn render_exprs(&self, exprs: impl IntoIterator<Item = VdSemExprIdx>) -> Vec<DisplayTree> {
        exprs
            .into_iter()
            .map(|expr| self.render_expr(expr))
            .collect()
    }

    pub fn render_expr(&self, expr: VdSemExprIdx) -> DisplayTree {
        let expr_range = self.expr_range_map[expr];
        let offset_range = match expr_range {
            VdSemExprTokenIdxRange::Standard(token_idx_range) => self
                .token_storage
                .token_idx_range_offset_range(token_idx_range),
        };
        let source = &self.input[offset_range];
        let value = match *self.expr_arena[expr].data() {
            VdSemExprData::Literal {
                token_idx_range,
                literal,
            } => format!("{:?} expr.literal", source),
            VdSemExprData::Letter { letter, .. } => format!("{:?} expr.letter", source),
            VdSemExprData::BaseOpr { opr } => format!("{:?} expr.base_opr", source),
            VdSemExprData::Binary {
                lopd, opr, ropd, ..
            } => format!("{:?} expr.binary", source),
            VdSemExprData::Prefix { opr, opd, .. } => format!("{:?} expr.prefix", source),
            VdSemExprData::Suffix { opd, opr, .. } => format!("{:?} expr.suffix", source),
            VdSemExprData::FoldingSeparatedList { .. } => {
                format!("{:?} expr.folding_separated_list", source)
            }
            VdSemExprData::ChainingSeparatedList { .. } => {
                format!("{:?} expr.chaining_separated_list", source)
            }
            VdSemExprData::Attach { .. } => format!("{:?} expr.attach", source),
            VdSemExprData::UniadicChain => format!("{:?} expr.uniadic_chain", source),
            VdSemExprData::VariadicChain => format!("{:?} expr.variadic_chain", source),
            VdSemExprData::UniadicArray => format!("{:?} expr.uniadic_array", source),
            VdSemExprData::VariadicArray => format!("{:?} expr.variadic_array", source),
            VdSemExprData::LxDelimited { .. } => format!("{:?} expr.latex_delimited", source),
            VdSemExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => format!("{:?} delimited", source),
            VdSemExprData::Frac {
                numerator,
                denominator,
                ..
            } => format!("{:?} fraction", source),
            VdSemExprData::Sqrt { radicand, .. } => format!("{:?} sqrt", source),
        };
        DisplayTree::new(
            value,
            self.render_exprs(self.expr_arena[expr].data().children()),
        )
    }

    pub fn render_all_stmts(&self, stmts: VdSemStmtIdxRange) -> DisplayTree {
        let stmts_range =
            self.stmt_range_map[stmts.start()].join(self.stmt_range_map[stmts.last().unwrap()]);
        let offset_range = self.token_storage.token_idx_range_offset_range(stmts_range);
        DisplayTree::new(
            self.input[offset_range].to_string(),
            self.render_stmts(stmts),
        )
    }

    pub fn render_stmts(&self, stmts: VdSemStmtIdxRange) -> Vec<DisplayTree> {
        stmts
            .into_iter()
            .map(|stmt| self.render_stmt(stmt))
            .collect()
    }

    pub fn render_stmt(&self, stmt: VdSemStmtIdx) -> DisplayTree {
        let stmt_range = self.stmt_range_map[stmt];
        let offset_range = self.token_storage.token_idx_range_offset_range(stmt_range);
        let source = &self.input[offset_range];
        let value = match *self.stmt_arena[stmt].data() {
            VdSemStmtData::Paragraph(arena_idx_range) => format!("{:?} stmt.paragraph", source),
            VdSemStmtData::Environment {
                environment_signature,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => format!("{:?} stmt.block", source),
        };
        DisplayTree::new(
            value,
            self.render_stmt_children(self.stmt_arena[stmt].data().children()),
        )
    }

    fn render_stmt_children(&self, children: Vec<VdSemStmtChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSemStmtChild::Sentence(sentence) => self.render_sentence(sentence),
                VdSemStmtChild::Stmt(stmt) => self.render_stmt(stmt),
            })
            .collect()
    }

    pub fn render_sentence(&self, sentence: VdSemSentenceIdx) -> DisplayTree {
        let sentence_range = self.sentence_range_map[sentence];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(sentence_range);
        let source = &self.input[offset_range];
        let value = match self.sentence_arena[sentence] {
            VdSemSentenceData::Clauses { clauses, end } => format!("{:?} sentence.clauses", source),
        };
        DisplayTree::new(
            value,
            self.render_sentence_children(self.sentence_arena[sentence].children()),
        )
    }

    fn render_sentence_children(&self, children: Vec<VdSemSentenceChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSemSentenceChild::Clause(clause) => self.render_clause(clause),
            })
            .collect()
    }

    pub fn render_clause(&self, clause: VdSemClauseIdx) -> DisplayTree {
        let clause_range = self.clause_range_map[clause];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(clause_range);
        let source = &self.input[offset_range];
        let value = match self.clause_arena[clause] {
            VdSemClauseData::Verb => todo!(),
            VdSemClauseData::Let { .. } => format!("{:?} clause.let", source),
            VdSemClauseData::Assume { .. } => format!("{:?} clause.assume", source),
            VdSemClauseData::Then { .. } => format!("{:?} clause.then", source),
            VdSemClauseData::Todo(lx_rose_token_idx) => format!("{:?} clause.todo", source),
        };
        DisplayTree::new(
            value,
            self.render_clause_children(self.clause_arena[clause].children()),
        )
    }

    fn render_clause_children(&self, children: Vec<VdSemClauseChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSemClauseChild::Expr(expr) => self.render_expr(expr),
            })
            .collect()
    }

    pub fn render_divisions(&self, divisions: VdSemDivisionIdxRange) -> Vec<DisplayTree> {
        divisions
            .into_iter()
            .map(|division| self.render_division(division))
            .collect()
    }

    pub fn render_division(&self, division: VdSemDivisionIdx) -> DisplayTree {
        let division_range = self.division_range_map[division];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(division_range);
        let source = &self.input[offset_range];
        let value = match *self.division_arena[division].data() {
            VdSemDivisionData::Stmts { stmts } => format!("{:?} division.stmts", source),
            VdSemDivisionData::Divisions { .. } => format!("{:?} division.divisions", source),
        };
        DisplayTree::new(
            value,
            self.division_arena[division]
                .data()
                .children()
                .into_iter()
                .map(|child| self.render_division_child(child))
                .collect(),
        )
    }

    fn render_division_child(&self, child: VdSemDivisionChild) -> DisplayTree {
        match child {
            VdSemDivisionChild::Division(division) => self.render_division(division),
            VdSemDivisionChild::Title(stmts) => {
                DisplayTree::new("title".to_string(), self.render_stmts(stmts))
            }
            VdSemDivisionChild::Stmt(stmt) => self.render_stmt(stmt),
        }
    }
}
