use super::*;
use crate::builder::VdLeanTranspilationBuilder;
use dictionary::VdLeanTranspilationDictionary;
use either::*;
use husky_tree_utils::display::DisplayTree;
use latex_prelude::mode::LxMode;
use lean_hir_expr::{
    expr::{LnHirExprArena, LnHirExprIdx},
    helpers::{
        fmt::{LnHirExprFormatter, LnHirExprFormatterConfig},
        show::display_tree::LnHirExprDisplayTreeBuilder,
    },
    stmt::{LnHirStmtArena, LnHirStmtIdxRange},
    tactic::LnHirTacticArena,
};
use visored_annotation::annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation};
use visored_hir_expr::{
    expr::VdHirExprIdx, stmt::VdHirStmtIdxRange, test_helpers::example::VdHirExprExample,
};

pub struct VdLeanTranspilationExample {
    expr_arena: LnHirExprArena,
    stmt_arena: LnHirStmtArena,
    tactic_arena: LnHirTacticArena,
    result: Either<LnHirExprIdx, LnHirStmtIdxRange>,
}

impl VdLeanTranspilationExample {
    pub fn new(
        input: &str,
        root_mode: LxMode,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
        db: &::salsa::Db,
    ) -> Self {
        let VdHirExprExample {
            expr_arena: vd_hir_expr_arena,
            stmt_arena: vd_hir_stmt_arena,
            result,
        } = VdHirExprExample::new(input, LxMode::Math, &[], &[], db);
        let dictionary = &VdLeanTranspilationDictionary::new_standard();
        let mut builder = VdLeanTranspilationBuilder::new(
            db,
            vd_hir_expr_arena.as_arena_ref(),
            vd_hir_stmt_arena.as_arena_ref(),
            dictionary,
        );
        let result = match result {
            Left(expr) => Left(expr.to_lean(&mut builder)),
            Right(stmts) => todo!(),
        };
        let (expr_arena, stmt_arena, tactic_arena) = builder.finish();
        Self {
            expr_arena,
            stmt_arena,
            tactic_arena,
            result,
        }
    }

    pub fn show_display_tree(&self, db: &::salsa::Db) -> String {
        self.display_tree(db).show(&Default::default())
    }

    fn display_tree(&self, db: &::salsa::Db) -> DisplayTree {
        let builder = LnHirExprDisplayTreeBuilder::new(
            db,
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
        );
        match self.result {
            Left(expr) => builder.render_expr(expr),
            Right(_) => todo!(),
        }
    }

    pub fn show_fmt(&self, db: &::salsa::Db) -> String {
        let fmt_config = Default::default();
        let mut formatter = self.formatter(db, &fmt_config);
        match self.result {
            Left(expr) => formatter.format_expr_ext(expr),
            Right(_) => todo!(),
        }
        formatter.finish()
    }

    fn formatter<'a>(
        &'a self,
        db: &'a ::salsa::Db,
        config: &'a LnHirExprFormatterConfig,
    ) -> LnHirExprFormatter<'a> {
        LnHirExprFormatter::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            config,
            db,
        )
    }
}
