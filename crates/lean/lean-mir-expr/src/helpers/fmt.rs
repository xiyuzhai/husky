use crate::{
    expr::{application::LnMirFunc, LnMirExprArenaRef, LnMirExprData, LnMirExprIdx},
    item_defn::{
        def::LnMirDefBody, LnItemDefnArenaRef, LnItemDefnData, LnItemDefnIdx, LnItemDefnIdxRange,
        LnMirItemDefnGroupMeta,
    },
    stmt::LnMirStmtArenaRef,
    tactic::{LnMirTacticArenaRef, LnMirTacticData, LnMirTacticIdx, LnMirTacticIdxRange},
};
use lean_opr::precedence::LnPrecedenceRange;
use lean_term::term::literal::LnLiteralData;
use std::fmt::Write;

pub struct LnMirExprFormatter<'a> {
    expr_arena: LnMirExprArenaRef<'a>,
    stmt_arena: LnMirStmtArenaRef<'a>,
    tactic_arena: LnMirTacticArenaRef<'a>,
    defn_arena: LnItemDefnArenaRef<'a>,
    config: &'a LnMirExprFormatterConfig,
    result: String,
    indent_level: usize,
}

pub struct LnMirExprFormatterConfig {
    line_max_len: usize,
    spaces_per_indent: usize,
}

impl Default for LnMirExprFormatterConfig {
    fn default() -> Self {
        Self {
            line_max_len: 80,
            spaces_per_indent: 2,
        }
    }
}

impl<'a> LnMirExprFormatter<'a> {
    pub fn new(
        expr_arena: LnMirExprArenaRef<'a>,
        stmt_arena: LnMirStmtArenaRef<'a>,
        tactic_arena: LnMirTacticArenaRef<'a>,
        defn_arena: LnItemDefnArenaRef<'a>,
        config: &'a LnMirExprFormatterConfig,
    ) -> Self {
        Self {
            expr_arena,
            stmt_arena,
            tactic_arena,
            defn_arena,
            config,
            result: Default::default(),
            indent_level: 0,
        }
    }
}

impl<'a> LnMirExprFormatter<'a> {
    pub fn format_expr_ext(&mut self, expr: LnMirExprIdx) {
        self.format_expr(expr, false, LnPrecedenceRange::Any);
    }

    fn format_expr(
        &mut self,
        expr: LnMirExprIdx,
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

    fn format_expr_inner(&mut self, expr: LnMirExprIdx, multiline: bool) {
        // Lean formatter rule: outer expressions should multiline prior to inner expressions.
        // This ensures that subexpressions only attempt multiline formatting if the parent is already multiline.
        let subexpr_try_multiline = multiline;
        let arena = self.expr_arena;
        match arena[expr] {
            LnMirExprData::ItemPath(item_path) => {
                self.result += &item_path.show();
            }
            LnMirExprData::Variable { ident } => {
                self.write_word(ident.data());
            }

            LnMirExprData::Lambda {
                ref parameters,
                body,
            } => {
                self.result.push('λ');
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        self.result.push(' ');
                    }
                    self.result += param.ident().data();
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
            LnMirExprData::Application {
                function,
                arguments,
            } => {
                match function {
                    LnMirFunc::BinaryOpr { opr, instantiation } => {
                        debug_assert_eq!(arguments.len(), 2);
                        let lopd = arguments.first().unwrap();
                        let ropd = arguments.last().unwrap();
                        self.format_expr(lopd, subexpr_try_multiline, opr.left_precedence_range());
                        self.result += opr.fmt_str();
                        self.format_expr(ropd, subexpr_try_multiline, opr.right_precedence_range());
                    }
                    LnMirFunc::PrefixOpr { opr, instantiation } => {
                        self.result += opr.fmt_str();
                        self.format_expr(
                            arguments.first().unwrap(),
                            subexpr_try_multiline,
                            opr.precedence_range(),
                        );
                    }
                    LnMirFunc::SuffixOpr { opr, instantiation } => todo!(),
                    LnMirFunc::Expr(expr) => {
                        self.format_expr(expr, subexpr_try_multiline, LnPrecedenceRange::Any);
                        for arg in arguments {
                            self.result.push(' ');
                            self.format_expr(arg, subexpr_try_multiline, LnPrecedenceRange::Any);
                        }
                    }
                    // ad hoc
                    LnMirFunc::InSet => self.result += "sorry",
                }
                // for expr in arguments {
                //     self.format_expr(
                //         expr,
                //         subexpr_try_multiline,
                //         LnPrecedenceRange::APPLICATION_SUBEXPR,
                //     );
                // }
                // LnMirExprData::Prefix { opr, opd } => {
                //                 self.result += opr.fmt_str();
                //                 self.format_expr(opd, subexpr_try_multiline, opr.precedence_range());
                //             }
                //             LnMirExprData::Suffix { opd, opr } => {
                //                 self.format_expr(opd, subexpr_try_multiline, opr.precedence_range());
                //                 self.result += opr.fmt_str();
                //             }
            }
            LnMirExprData::Literal(lit) => {
                self.result += match lit.data() {
                    LnLiteralData::Nat(s) => s,
                    LnLiteralData::Float(s) => s,
                }
            }
            LnMirExprData::Sorry => self.write_word("sorry"),
        }
    }

    fn write_word(&mut self, s: &str) {
        if !(self.result.ends_with(['(', ' ', '\n']) || self.result.is_empty()) {
            self.result.push(' ');
        }
        self.result += s;
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

    pub fn format_defns(&mut self, defns: LnItemDefnIdxRange) {
        for (i, defn) in defns.into_iter().enumerate() {
            if i > 0 {
                self.result += "\n";
            }
            self.format_defn(defn);
        }
    }

    pub fn format_defn(&mut self, defn: LnItemDefnIdx) {
        self.make_sure_new_paragraph();
        let defn_arena = self.defn_arena;
        match defn_arena[defn] {
            LnItemDefnData::Variable { ident: symbol, ty } => {
                write!(self.result, "variable ({} : ", symbol.data());
                self.format_expr_ext(ty);
                write!(self.result, ")");
            }
            LnItemDefnData::Group { defns, ref meta } => {
                self.make_sure_new_paragraph();
                if let LnMirItemDefnGroupMeta::Division(Some(namespace))
                | LnMirItemDefnGroupMeta::Environment(namespace) = *meta
                    && let Some(ident) = namespace.ident()
                {
                    self.make_sure_new_paragraph();
                    write!(self.result, "namespace {}\n", ident.data());
                }
                self.format_defns(defns);
                if let LnMirItemDefnGroupMeta::Division(Some(namespace))
                | LnMirItemDefnGroupMeta::Environment(namespace) = *meta
                    && let Some(ident) = namespace.ident()
                {
                    self.make_sure_new_line();
                    write!(self.result, "end {}\n", ident.data());
                }
            }
            LnItemDefnData::Def { symbol, ty, body } => {
                write!(self.result, "def {} : ", symbol.data());
                self.format_expr_ext(ty);
                self.result += " := ";
                self.format_def_body(body);
            }
        }
    }

    pub fn format_def_body(&mut self, body: LnMirDefBody) {
        match body {
            LnMirDefBody::Expr(expr) => self.format_expr_ext(expr),
            LnMirDefBody::Tactics(tactics) => {
                self.result += "by";
                self.indented(|slf| slf.format_tactics(tactics))
            }
            LnMirDefBody::Stmts(stmts) => todo!(),
        }
    }

    pub fn format_tactics(&mut self, tactics: LnMirTacticIdxRange) {
        for tactic in tactics {
            self.format_tactic(tactic);
        }
    }

    fn format_tactic(&mut self, tactic: LnMirTacticIdx) {
        self.make_sure_new_line();
        let tactic_arena = self.tactic_arena;
        match tactic_arena[tactic] {
            LnMirTacticData::Obtain => todo!(),
            LnMirTacticData::Exact => todo!(),
            LnMirTacticData::Cases => todo!(),
            LnMirTacticData::Rcases => todo!(),
            LnMirTacticData::Have => todo!(),
            LnMirTacticData::Show => todo!(),
            LnMirTacticData::Calc {
                leader,
                ref followers,
            } => {
                self.result += "calc";
                self.indented(|slf| {
                    for (i, ((opr, _), follower)) in followers.iter().copied().enumerate() {
                        slf.make_sure_new_line();
                        if i == 0 {
                            slf.format_expr_ext(leader);
                            slf.result += opr.fmt_str();
                            slf.format_expr_ext(follower);
                            slf.result += " := sorry"
                        } else {
                            slf.result += "_";
                            slf.result += opr.fmt_str();
                            slf.format_expr_ext(follower);
                            slf.result += " := sorry"
                        }
                    }
                });
            }
            LnMirTacticData::Sorry => {
                self.result += "sorry";
            }
        }
    }

    fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indent_level += 1;
        f(self);
        self.indent_level -= 1;
    }

    fn make_sure_new_line(&mut self) {
        if !self.result.is_empty() && !self.result.ends_with('\n') {
            self.result += "\n";
        }
        for _ in 0..(self.indent_level * self.config.spaces_per_indent) {
            self.result.push(' ');
        }
    }

    fn make_sure_new_paragraph(&mut self) {
        self.make_sure_new_line();
        if !self.result.is_empty() {
            let last_line = self.result.lines().last().unwrap_or("");
            if !last_line.starts_with("namespace")
                && !last_line.starts_with("section")
                && !self.result.ends_with("\n\n")
            {
                self.result += "\n";
            }
        }
    }

    pub fn finish(self) -> String {
        self.result
    }
}
