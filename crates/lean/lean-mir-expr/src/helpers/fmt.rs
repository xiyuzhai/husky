use crate::{
    expr::{application::LnMirFunc, LnMirExprArenaRef, LnMirExprData, LnMirExprIdx},
    helpers::compare::ln_mir_expr_deep_eq,
    item_defn::{
        def::LnMirDefBody, LnItemDefnArenaRef, LnItemDefnComment, LnItemDefnData, LnItemDefnIdx,
        LnItemDefnIdxRange, LnItemDefnOrderedMap, LnMirItemDefnGroupMeta,
    },
    stmt::LnMirStmtArenaRef,
    tactic::{LnMirTacticArenaRef, LnMirTacticData, LnMirTacticIdx, LnMirTacticIdxRange},
};
use eterned::db::EternerDb;
use lean_opr::{
    opr::binary::LnBinaryOpr,
    precedence::{LnPrecedence, LnPrecedenceRange},
};
use lean_term::term::literal::LnLiteralData;
use std::fmt::Write;

pub struct LnMirExprFormatter<'a> {
    db: &'a EternerDb,
    expr_arena: LnMirExprArenaRef<'a>,
    stmt_arena: LnMirStmtArenaRef<'a>,
    tactic_arena: LnMirTacticArenaRef<'a>,
    defn_arena: LnItemDefnArenaRef<'a>,
    defn_comments: &'a LnItemDefnOrderedMap<LnItemDefnComment>,
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
        db: &'a EternerDb,
        expr_arena: LnMirExprArenaRef<'a>,
        stmt_arena: LnMirStmtArenaRef<'a>,
        tactic_arena: LnMirTacticArenaRef<'a>,
        defn_arena: LnItemDefnArenaRef<'a>,
        defn_comments: &'a LnItemDefnOrderedMap<LnItemDefnComment>,
        config: &'a LnMirExprFormatterConfig,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
            tactic_arena,
            defn_arena,
            defn_comments,
            config,
            result: Default::default(),
            indent_level: 0,
        }
    }
}

impl<'a> LnMirExprFormatter<'a> {
    pub fn db(&self) -> &'a EternerDb {
        self.db
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
        let expr_arena = self.expr_arena;
        let expr_entry = &expr_arena[expr];
        let expr_data = expr_entry.data();
        let needs_bracket = (!precedence_range.include(expr_data.outer_precedence()))
            || expr_entry.ty_ascription().is_some();
        if needs_bracket {
            // TODO: consider multiline
            self.result += "(";
        }
        let prev_len = self.result.len();
        self.format_expr_inner(expr, false);
        if let Some(ty_ascription) = expr_entry.ty_ascription() {
            self.result += " : ";
            self.format_expr_ext(ty_ascription);
        }
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
        let db = self.db();
        // Lean formatter rule: outer expressions should multiline prior to inner expressions.
        // This ensures that subexpressions only attempt multiline formatting if the parent is already multiline.
        let subexpr_try_multiline = multiline;
        let arena = self.expr_arena;
        match *arena[expr].data() {
            LnMirExprData::ItemPath(item_path) => {
                self.result += &item_path.show(db);
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
                        self.format_expr(
                            expr,
                            subexpr_try_multiline,
                            LnPrecedenceRange::APPLICATION_SUBEXPR,
                        );
                        for arg in arguments {
                            self.result.push(' ');
                            self.format_expr(
                                arg,
                                subexpr_try_multiline,
                                LnPrecedenceRange::APPLICATION_SUBEXPR,
                            );
                        }
                    }
                    // ad hoc
                    LnMirFunc::InSet => self.result += "in_set",
                    LnMirFunc::Iff => {
                        let mut args = arguments.into_iter();
                        let a = args.next().unwrap();
                        let b = args.next().unwrap();
                        self.format_expr(a, subexpr_try_multiline, LnPrecedenceRange::IFF_LEFT);
                        self.result += " ↔ ";
                        self.format_expr(b, subexpr_try_multiline, LnPrecedenceRange::IFF_RIGHT);
                    }
                }
            }
            LnMirExprData::Literal(lit) => {
                self.result += match lit.data() {
                    LnLiteralData::Nat(s) => s,
                    LnLiteralData::Int(s) => s,
                    LnLiteralData::Frac(s) => s,
                }
            }
            LnMirExprData::Sorry => self.write_word("sorry"),
            LnMirExprData::By { tactics } => {
                self.result += "by";
                debug_assert!(!tactics.is_empty());
                if tactics.len() == 1 {
                    self.result += " ";
                    self.format_tactic(tactics.first().unwrap());
                } else {
                    self.indented(|slf| slf.format_tactics(tactics));
                }
            }
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
        let db = self.db();
        self.make_sure_new_paragraph();
        self.format_defn_comment(defn);
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
            LnItemDefnData::Def {
                ident,
                ref parameters,
                ty,
                body,
            } => {
                write!(self.result, "def {}", ident.data());
                // Group consecutive parameters with the same type
                let mut current_group = Vec::new();
                let mut current_ty = None;

                for param in parameters {
                    if let Some(ty) = current_ty {
                        if ln_mir_expr_deep_eq(ty, param.ty, self.expr_arena) {
                            current_group.push(param.ident.data());
                        } else {
                            // Print current group
                            write!(self.result, " ({} : ", current_group.join(" "));
                            self.format_expr_ext(ty);
                            write!(self.result, ")");

                            // Start new group
                            current_group = vec![param.ident.data()];
                            current_ty = Some(param.ty);
                        }
                    } else {
                        // First parameter
                        current_group.push(param.ident.data());
                        current_ty = Some(param.ty);
                    }
                }

                // Print final group if any
                if let Some(ty) = current_ty {
                    write!(self.result, " ({} : ", current_group.join(" "));
                    self.format_expr_ext(ty);
                    write!(self.result, ")");
                }
                if let Some(ty) = ty {
                    write!(self.result, " : ");
                    self.format_expr_ext(ty);
                }
                self.result += " := ";
                self.format_def_body(body);
            }
        }
    }

    pub fn format_defn_comment(&mut self, defn: LnItemDefnIdx) {
        let comment = &self.defn_comments[defn];
        match *comment {
            LnItemDefnComment::Void => {}
            LnItemDefnComment::Lines(ref lines) => {
                for line in lines {
                    self.make_sure_new_line();
                    self.result += "-- ";
                    self.result += line;
                }
                self.make_sure_new_line();
            }
            LnItemDefnComment::Qed => {
                self.make_sure_new_line();
                self.result += "-- qed";
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
            self.make_sure_new_line();
            self.format_tactic(tactic);
        }
    }

    fn format_tactic(&mut self, tactic: LnMirTacticIdx) {
        let tactic_arena = self.tactic_arena;
        match tactic_arena[tactic] {
            LnMirTacticData::Intro { .. } => todo!(),
            LnMirTacticData::Obtain { .. } => todo!(),
            LnMirTacticData::Exact { term } => {
                write!(self.result, "exact ");
                self.format_expr_ext(term);
            }
            LnMirTacticData::Cases { .. } => todo!(),
            LnMirTacticData::Rcases { .. } => todo!(),
            LnMirTacticData::Have {
                ident,
                ty,
                construction,
            } => {
                write!(self.result, "have {}", ident.data());
                if let Some(ty) = ty {
                    write!(self.result, " : ");
                    self.format_expr_ext(ty);
                }
                write!(self.result, " := ");
                self.format_expr_ext(construction);
            }
            LnMirTacticData::Let {
                ident,
                ty,
                construction,
            } => {
                write!(self.result, "let {}", ident.data());
                if let Some(ty) = ty {
                    write!(self.result, " : ");
                    self.format_expr_ext(ty);
                }
                write!(self.result, " := ");
                self.format_expr_ext(construction);
            }
            LnMirTacticData::Show { ty, tactics } => {
                write!(self.result, "show ");
                self.format_expr_ext(ty);
                write!(self.result, " by");
                if tactics.len() == 1 {
                    self.result += " ";
                    self.format_tactic(tactics.first().unwrap());
                } else {
                    self.indented(|slf| slf.format_tactics(tactics));
                }
            }
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
                            // AD HOC
                            slf.result += " := by obvious"
                        } else {
                            slf.result += "_";
                            slf.result += opr.fmt_str();
                            slf.format_expr_ext(follower);
                            // AD HOC
                            slf.result += " := by obvious"
                        }
                    }
                });
            }
            LnMirTacticData::Obvious => {
                self.result += "obvious";
            }
            LnMirTacticData::Sorry => {
                self.result += "sorry";
            }
            LnMirTacticData::First { arms } => {
                self.result += "first";
                for arm in arms {
                    self.make_sure_new_line();
                    self.result += "| ";
                    self.format_tactic(arm);
                }
            }
            LnMirTacticData::Apply { hypothesis } => {
                self.result += "apply ";
                self.format_expr_ext(hypothesis);
            }
            LnMirTacticData::Custom {
                name,
                arguments,
                construction,
            } => {
                self.result += name;
                if let Some(arguments) = arguments {
                    for arg in arguments {
                        self.result += " ";
                        self.format_expr_ext(arg);
                    }
                }
                if let Some(construction) = construction {
                    self.result += " := ";
                    self.format_expr_ext(construction);
                }
            }
            LnMirTacticData::Assumption => {
                self.result += "assumption";
            }
        }
    }

    fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.make_sure_new_line();
        self.indent_level += 1;
        f(self);
        self.indent_level -= 1;
    }

    fn make_sure_new_line(&mut self) {
        let result_trimmed = self.result.trim_end_matches(' ');
        if !result_trimmed.is_empty() && !result_trimmed.ends_with('\n') {
            self.result += "\n";
        }
        let number_of_existing_spaces = self.result.len() - self.result.trim_end_matches(' ').len();
        for _ in number_of_existing_spaces..(self.indent_level * self.config.spaces_per_indent) {
            self.result.push(' ');
        }
    }

    fn make_sure_new_paragraph(&mut self) {
        debug_assert_eq!(self.indent_level, 0);
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
