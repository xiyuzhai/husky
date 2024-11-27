use crate::{
    builder::VdSynExprBuilder,
    clause::{VdSynClauseArenaRef, VdSynClauseChild, VdSynClauseData, VdSynClauseIdx},
    division::{
        VdSynDivisionArenaRef, VdSynDivisionChild, VdSynDivisionData, VdSynDivisionIdx,
        VdSynDivisionIdxRange,
    },
    expr::{VdSynExprArenaRef, VdSynExprData, VdSynExprIdx, VdSynExprIdxRange},
    phrase::VdSynPhraseArenaRef,
    range::{
        VdSynClauseTokenIdxRangeMap, VdSynDivisionTokenIdxRangeMap, VdSynExprTokenIdxRange,
        VdSynExprTokenIdxRangeMap, VdSynPhraseTokenIdxRangeMap, VdSynSentenceTokenIdxRangeMap,
        VdSynStmtTokenIdxRangeMap,
    },
    sentence::{VdSynSentenceArenaRef, VdSynSentenceChild, VdSynSentenceData, VdSynSentenceIdx},
    stmt::{VdSynStmtArenaRef, VdSynStmtChild, VdSynStmtData, VdSynStmtIdx, VdSynStmtIdxRange},
};
use husky_text_protocol::offset::TextOffsetRange;
use husky_tree_utils::display::DisplayTree;
use latex_ast::{
    ast::{
        math::{LxMathAstIdx, LxMathAstIdxRange},
        rose::{LxRoseAstIdx, LxRoseAstIdxRange},
        LxAstArenaRef, LxAstIdx, LxAstIdxRange,
    },
    range::LxAstTokenIdxRangeMap,
};
use latex_token::storage::LxTokenStorage;
use latex_vfs::path::LxFilePath;

pub struct VdSynExprDisplayTreeBuilder<'a> {
    input: &'a str,
    token_storage: &'a LxTokenStorage,
    ast_arena: LxAstArenaRef<'a>,
    ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
    expr_arena: VdSynExprArenaRef<'a>,
    phrase_arena: VdSynPhraseArenaRef<'a>,
    clause_arena: VdSynClauseArenaRef<'a>,
    sentence_arena: VdSynSentenceArenaRef<'a>,
    stmt_arena: VdSynStmtArenaRef<'a>,
    division_arena: VdSynDivisionArenaRef<'a>,
    expr_range_map: &'a VdSynExprTokenIdxRangeMap,
    phrase_range_map: &'a VdSynPhraseTokenIdxRangeMap,
    clause_range_map: &'a VdSynClauseTokenIdxRangeMap,
    sentence_range_map: &'a VdSynSentenceTokenIdxRangeMap,
    stmt_range_map: &'a VdSynStmtTokenIdxRangeMap,
    division_range_map: &'a VdSynDivisionTokenIdxRangeMap,
}

/// # construction
impl<'a> VdSynExprDisplayTreeBuilder<'a> {
    pub fn new(
        input: &'a str,
        token_storage: &'a LxTokenStorage,
        ast_arena: LxAstArenaRef<'a>,
        ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
        expr_arena: VdSynExprArenaRef<'a>,
        phrase_arena: VdSynPhraseArenaRef<'a>,
        clause_arena: VdSynClauseArenaRef<'a>,
        sentence_arena: VdSynSentenceArenaRef<'a>,
        stmt_arena: VdSynStmtArenaRef<'a>,
        division_arena: VdSynDivisionArenaRef<'a>,
        expr_range_map: &'a VdSynExprTokenIdxRangeMap,
        phrase_range_map: &'a VdSynPhraseTokenIdxRangeMap,
        clause_range_map: &'a VdSynClauseTokenIdxRangeMap,
        sentence_range_map: &'a VdSynSentenceTokenIdxRangeMap,
        stmt_range_map: &'a VdSynStmtTokenIdxRangeMap,
        division_range_map: &'a VdSynDivisionTokenIdxRangeMap,
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

/// # actions
impl<'a> VdSynExprDisplayTreeBuilder<'a> {
    pub fn render_all_exprs(&self, exprs: VdSynExprIdxRange) -> DisplayTree {
        // TODO: maybe just use the range covered by these exprs
        DisplayTree::new(self.input.to_string(), self.render_exprs(exprs))
    }

    pub fn render_exprs(&self, exprs: impl IntoIterator<Item = VdSynExprIdx>) -> Vec<DisplayTree> {
        exprs
            .into_iter()
            .map(|expr| self.render_expr(expr))
            .collect()
    }

    pub fn render_expr(&self, expr: VdSynExprIdx) -> DisplayTree {
        let expr_range = self.expr_range_map[expr];
        let offset_range = match expr_range {
            VdSynExprTokenIdxRange::Standard(token_idx_range) => self
                .token_storage
                .token_idx_range_offset_range(token_idx_range),
        };
        let source = &self.input[offset_range];
        let value = match self.expr_arena[expr] {
            VdSynExprData::Literal {
                token_idx_range,
                literal,
            } => format!("{:?} expr.literal", source),
            VdSynExprData::Letter { letter, .. } => format!("{:?} expr.letter", source),
            VdSynExprData::BaseOpr { opr } => format!("{:?} expr.base_opr", source),
            VdSynExprData::Binary { lopd, opr, ropd } => format!("{:?} expr.binary", source),
            VdSynExprData::Prefix { opr, opd } => format!("{:?} expr.prefix", source),
            VdSynExprData::Suffix { opd, opr } => format!("{:?} expr.suffix", source),
            VdSynExprData::SeparatedList { .. } => format!("{:?} expr.separated_list", source),
            VdSynExprData::Attach { base, ref scripts } => format!("{:?} expr.attach", source),
            VdSynExprData::UniadicChain => format!("{:?} expr.uniadic_chain", source),
            VdSynExprData::VariadicChain => format!("{:?} expr.variadic_chain", source),
            VdSynExprData::UniadicArray => format!("{:?} expr.uniadic_array", source),
            VdSynExprData::VariadicArray => format!("{:?} expr.variadic_array", source),
            VdSynExprData::Err(ref error) => format!("{:?} expr.error", source),
            VdSynExprData::LxDelimited { .. } => format!("{:?} expr.latex_delimited", source),
            VdSynExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => format!("{:?} delimited", source),
            VdSynExprData::Fraction {
                numerator,
                denominator,
                ..
            } => format!("{:?} fraction", source),
            VdSynExprData::Sqrt { radicand, .. } => format!("{:?} sqrt", source),
        };
        DisplayTree::new(value, self.render_exprs(self.expr_arena[expr].children()))
    }

    pub fn render_clause(&self, clause: VdSynClauseIdx) -> DisplayTree {
        let clause_range = self.clause_range_map[clause];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(clause_range);
        let source = &self.input[offset_range];
        let value = match self.clause_arena[clause] {
            VdSynClauseData::Let { .. } => format!("{:?} clause.let", source),
            VdSynClauseData::Assume { .. } => format!("{:?} clause.assume", source),
            VdSynClauseData::Then { .. } => format!("{:?} clause.then", source),
            VdSynClauseData::Todo(..) => format!("{:?} clause.todo", source),
        };
        DisplayTree::new(
            value,
            self.render_clause_children(self.clause_arena[clause].children()),
        )
    }

    fn render_clause_children(&self, children: Vec<VdSynClauseChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSynClauseChild::Expr(expr) => self.render_expr(expr),
            })
            .collect()
    }

    pub fn render_sentence(&self, sentence: VdSynSentenceIdx) -> DisplayTree {
        let sentence_range = self.sentence_range_map[sentence];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(sentence_range);
        let source = &self.input[offset_range];
        let value = match self.sentence_arena[sentence] {
            VdSynSentenceData::Clauses { clauses, end } => format!("{:?} sentence.clauses", source),
        };
        DisplayTree::new(
            value,
            self.render_sentence_children(self.sentence_arena[sentence].children()),
        )
    }

    fn render_sentence_children(&self, children: Vec<VdSynSentenceChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSynSentenceChild::Clause(clause) => self.render_clause(clause),
            })
            .collect()
    }

    pub fn render_all_stmts(&self, stmts: VdSynStmtIdxRange) -> DisplayTree {
        let stmts_range =
            self.stmt_range_map[stmts.start()].join(self.stmt_range_map[stmts.last().unwrap()]);
        let offset_range = self.token_storage.token_idx_range_offset_range(stmts_range);
        DisplayTree::new(
            self.input[offset_range].to_string(),
            self.render_stmts(stmts),
        )
    }

    pub fn render_stmts(&self, stmts: VdSynStmtIdxRange) -> Vec<DisplayTree> {
        stmts
            .into_iter()
            .map(|stmt| self.render_stmt(stmt))
            .collect()
    }

    pub fn render_stmt(&self, stmt: VdSynStmtIdx) -> DisplayTree {
        let stmt_range = self.stmt_range_map[stmt];
        let offset_range = self.token_storage.token_idx_range_offset_range(stmt_range);
        let source = &self.input[offset_range];
        let value = match self.stmt_arena[stmt] {
            VdSynStmtData::Paragraph(arena_idx_range) => format!("{:?} stmt.paragraph", source),
            VdSynStmtData::Environment { .. } => format!("{:?} stmt.block", source),
        };
        DisplayTree::new(
            value,
            self.render_stmt_children(self.stmt_arena[stmt].children()),
        )
    }

    fn render_stmt_children(&self, children: Vec<VdSynStmtChild>) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| match child {
                VdSynStmtChild::Sentence(sentence) => self.render_sentence(sentence),
                VdSynStmtChild::Stmt(stmt) => self.render_stmt(stmt),
            })
            .collect()
    }

    pub fn render_divisions(&self, divisions: VdSynDivisionIdxRange) -> Vec<DisplayTree> {
        divisions
            .into_iter()
            .map(|division| self.render_division(division))
            .collect()
    }

    fn render_division(&self, division: VdSynDivisionIdx) -> DisplayTree {
        let division_range = self.division_range_map[division];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(division_range);
        let source = &self.input[offset_range];
        let value = match self.division_arena[division] {
            VdSynDivisionData::Stmts { .. } => format!("{:?} division.stmts", source),
            VdSynDivisionData::Divisions { level, .. } => {
                format!("{:?} division.{level}", source)
            }
        };
        DisplayTree::new(
            value,
            self.division_arena[division]
                .children()
                .into_iter()
                .map(|child| self.render_division_child(child))
                .collect(),
        )
    }

    fn render_division_child(&self, child: VdSynDivisionChild) -> DisplayTree {
        match child {
            VdSynDivisionChild::Division(division) => self.render_division(division),
            VdSynDivisionChild::Stmt(stmt) => self.render_stmt(stmt),
            VdSynDivisionChild::Title(stmts) => {
                DisplayTree::new("title".to_string(), self.render_stmts(stmts))
            }
        }
    }

    fn ast_offset_range(&self, ast: LxAstIdx) -> TextOffsetRange {
        match ast {
            LxAstIdx::Lisp(ast) => todo!(),
            LxAstIdx::Math(ast) => self.math_ast_offset_range(ast),
            LxAstIdx::Root(ast) => todo!(),
            LxAstIdx::Rose(ast) => self.rose_ast_offset_range(ast),
        }
    }

    fn math_ast_offset_range(&self, ast: LxMathAstIdx) -> TextOffsetRange {
        let range = self.ast_token_idx_range_map[ast];
        self.token_storage.token_idx_range_offset_range(range)
    }

    fn rose_ast_offset_range(&self, ast: LxRoseAstIdx) -> TextOffsetRange {
        let range = self.ast_token_idx_range_map[ast];
        self.token_storage.token_idx_range_offset_range(range)
    }

    fn asts_offset_range(&self, asts: LxAstIdxRange) -> TextOffsetRange {
        match asts {
            LxAstIdxRange::Lisp(asts) => todo!(),
            LxAstIdxRange::Math(asts) => self.math_asts_offset_range(asts),
            LxAstIdxRange::Root(asts) => todo!(),
            LxAstIdxRange::Rose(asts) => self.rose_asts_offset_range(asts),
        }
    }

    fn math_asts_offset_range(&self, asts: LxMathAstIdxRange) -> TextOffsetRange {
        let first = asts.start();
        let Some(last) = asts.last() else {
            return (0..0).into();
        };
        self.math_ast_offset_range(first)
            .join(self.math_ast_offset_range(last))
    }

    fn rose_asts_offset_range(&self, asts: LxRoseAstIdxRange) -> TextOffsetRange {
        let first = asts.start();
        let Some(last) = asts.last() else { todo!() };
        self.rose_ast_offset_range(first)
            .join(self.rose_ast_offset_range(last))
    }
}
