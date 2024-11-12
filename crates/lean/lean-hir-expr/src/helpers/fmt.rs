use crate::{
    expr::{LnHirExprArenaRef, LnHirExprData, LnHirExprIdx},
    stmt::LnHirStmtArenaRef,
    tactic::LnHirTacticArenaRef,
};
use lean_opr::precedence::LnPrecedenceRange;
use lean_term::term::literal::LnLiteralData;

pub struct LnHirExprFormatter<'a> {
    db: &'a ::salsa::Db,
    expr_arena: LnHirExprArenaRef<'a>,
    stmt_arena: LnHirStmtArenaRef<'a>,
    tactic_arena: LnHirTacticArenaRef<'a>,
    config: &'a LnHirExprFormatterConfig,
    result: String,
}

pub struct LnHirExprFormatterConfig {
    line_max_len: usize,
}

impl Default for LnHirExprFormatterConfig {
    fn default() -> Self {
        Self { line_max_len: 80 }
    }
}

impl<'a> LnHirExprFormatter<'a> {
    pub fn new(
        expr_arena: LnHirExprArenaRef<'a>,
        stmt_arena: LnHirStmtArenaRef<'a>,
        tactic_arena: LnHirTacticArenaRef<'a>,
        config: &'a LnHirExprFormatterConfig,
        db: &'a ::salsa::Db,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
            tactic_arena,
            config,
            result: Default::default(),
        }
    }
}

impl<'a> LnHirExprFormatter<'a> {
    pub fn format_expr_ext(&mut self, expr: LnHirExprIdx) {
        self.format_expr(expr, false, LnPrecedenceRange::Any);
    }

    fn format_expr(
        &mut self,
        expr: LnHirExprIdx,
        try_multiline: bool,
        precedence_range: LnPrecedenceRange,
    ) {
        let needs_bracket = !precedence_range.include(self.expr_arena[expr].outer_precedence());
        if needs_bracket {
            // TODO: consider multiline
            self.result += "(";
        }
        let prev_len = self.result.len();
        self.format_expr_inner(expr, false);
        if try_multiline && !self.check_lines(prev_len) {
            self.result.truncate(prev_len);
            self.format_expr_inner(expr, true);
        }
        if needs_bracket {
            // TODO: consider multiline
            self.result += ")";
        }
    }

    fn format_expr_inner(&mut self, expr: LnHirExprIdx, multiline: bool) {
        // Lean formatter rule: outer expressions should multiline prior to inner expressions.
        // This ensures that subexpressions only attempt multiline formatting if the parent is already multiline.
        let subexpr_try_multiline = multiline;
        let db = self.db;
        let arena = self.expr_arena;
        match arena[expr] {
            LnHirExprData::ItemPath(item_path) => {
                self.result += &item_path.show(db);
            }
            LnHirExprData::Variable { ident } => {
                if !self.result.ends_with(['(', ' ']) {
                    self.result.push(' ');
                }
                self.result += ident.data(db)
            }
            LnHirExprData::Prefix { opr, opd } => {
                self.result += opr.fmt_str();
                self.format_expr(opd, subexpr_try_multiline, opr.precedence_range());
            }
            LnHirExprData::Suffix { opd, opr } => {
                self.format_expr(opd, subexpr_try_multiline, opr.precedence_range());
                self.result += opr.fmt_str();
            }
            LnHirExprData::Binary { lopd, opr, ropd } => {
                self.format_expr(lopd, subexpr_try_multiline, opr.left_precedence_range());
                if !self.result.ends_with(' ') {
                    self.result.push(' ');
                }
                self.result += opr.fmt_str();
                self.result.push(' ');
                self.format_expr(ropd, subexpr_try_multiline, opr.right_precedence_range());
            }
            LnHirExprData::Lambda {
                ref parameters,
                body,
            } => {
                self.result.push('λ');
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        self.result.push(' ');
                    }
                    self.result += param.ident().data(db);
                    self.result.push_str(" : ");
                    self.format_expr(param.ty(), false, LnPrecedenceRange::Any);
                }
                self.result += " => ";
                if multiline {
                    self.result.push('\n');
                    self.result.push_str("  "); // Indent the body
                }
                self.format_expr(body, multiline, LnPrecedenceRange::Any);
            }
            LnHirExprData::Application {
                function_and_arguments,
            } => {
                for expr in function_and_arguments {
                    self.format_expr(
                        expr,
                        subexpr_try_multiline,
                        LnPrecedenceRange::APPLICATION_SUBEXPR,
                    );
                }
            }
            LnHirExprData::Literal(lit) => {
                self.result += match lit.data(db) {
                    LnLiteralData::Nat(s) => s,
                }
            }
        }
    }

    fn check_lines(&self, prev_len: usize) -> bool {
        // Find the end of the previous line
        let prev_line_end_offset = self.result[..prev_len]
            .rfind('\n')
            .map(|i| i + 1)
            .unwrap_or(0);

        // Check all lines from the previous line end
        self.result[prev_line_end_offset..]
            .lines()
            .all(|line| line.len() <= self.config.line_max_len)
    }

    pub fn finish(self) -> String {
        self.result
    }
}
