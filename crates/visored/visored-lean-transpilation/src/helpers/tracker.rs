use super::*;
use crate::dictionary::VdLeanDictionary;
use crate::{builder::VdLeanTranspilationBuilder, VdTranspileToLean};
use either::*;
use husky_tree_utils::display::DisplayTree;
use latex_prelude::{
    helper::tracker::{LxDocumentBodyInput, LxDocumentInput, LxFormulaInput, LxPageInput},
    mode::LxMode,
};
use lean_mir_expr::{
    expr::{LnMirExprArena, LnMirExprIdx},
    helpers::{
        fmt::{LnMirExprFormatter, LnMirExprFormatterConfig},
        show::display_tree::LnMirExprDisplayTreeBuilder,
    },
    item_defn::{LnItemDefnArena, LnItemDefnIdxRange},
    stmt::{LnMirStmtArena, LnMirStmtIdxRange},
    tactic::LnMirTacticArena,
};
use visored_annotation::annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation};
use visored_mir_expr::{
    expr::VdMirExprIdx,
    helpers::tracker::{IsVdMirExprInput, VdMirExprTracker},
    stmt::VdMirStmtIdxRange,
};

pub struct VdLeanTranspilationTracker<'a, Input: IsVdLeanTranspilationInput<'a>> {
    expr_arena: LnMirExprArena,
    stmt_arena: LnMirStmtArena,
    tactic_arena: LnMirTacticArena,
    defn_arena: LnItemDefnArena,
    output: Input::VdLeanTranspilationOutput,
}

pub trait IsVdLeanTranspilationInput<'a>: IsVdMirExprInput<'a> + Copy {
    type VdLeanTranspilationOutput: IsVdLeanTranspilationOutput
        + FromVdTranspileToLean<Self::VdMirExprOutput>;
}

pub trait IsVdLeanTranspilationOutput: std::fmt::Debug + Copy {
    fn show_display_tree(self, builder: &LnMirExprDisplayTreeBuilder) -> String;
    fn show_fmt(self, formatter: &mut LnMirExprFormatter);
}

pub trait FromVdTranspileToLean<S> {
    fn from_transpile_to_lean(s: S, builder: &mut VdLeanTranspilationBuilder) -> Self;
}

impl<S, T> FromVdTranspileToLean<S> for T
where
    S: VdTranspileToLean<T>,
{
    fn from_transpile_to_lean(s: S, builder: &mut VdLeanTranspilationBuilder) -> Self {
        s.to_lean(builder)
    }
}

impl<'a, Input: IsVdLeanTranspilationInput<'a>> VdLeanTranspilationTracker<'a, Input> {
    pub fn new(
        input: Input,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
        db: &::salsa::Db,
    ) -> Self {
        let VdMirExprTracker {
            root_module_path,
            expr_arena: vd_mir_expr_arena,
            stmt_arena: vd_mir_stmt_arena,
            symbol_local_defn_storage: vd_mir_symbol_local_defn_storage,
            output,
        } = VdMirExprTracker::new(input, &[], &[], db);
        let dictionary = &VdLeanDictionary::new_standard(db);
        let mut builder = VdLeanTranspilationBuilder::new(
            db,
            vd_mir_expr_arena.as_arena_ref(),
            vd_mir_stmt_arena.as_arena_ref(),
            &vd_mir_symbol_local_defn_storage,
            dictionary,
            root_module_path,
        );
        let output = FromVdTranspileToLean::from_transpile_to_lean(output, &mut builder);
        let (expr_arena, stmt_arena, tactic_arena, defn_arena) = builder.finish();
        Self {
            expr_arena,
            stmt_arena,
            tactic_arena,
            defn_arena,
            output,
        }
    }

    pub fn show_display_tree(&self, db: &::salsa::Db) -> String {
        let builder = LnMirExprDisplayTreeBuilder::new(
            db,
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            self.defn_arena.as_arena_ref(),
        );
        self.output.show_display_tree(&builder)
    }

    pub fn show_fmt(&self, db: &::salsa::Db) -> String {
        let fmt_config = Default::default();
        let mut formatter = self.formatter(db, &fmt_config);
        self.output.show_fmt(&mut formatter);
        formatter.finish()
    }

    fn formatter<'b>(
        &'b self,
        db: &'b ::salsa::Db,
        config: &'b LnMirExprFormatterConfig,
    ) -> LnMirExprFormatter<'b> {
        LnMirExprFormatter::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            self.defn_arena.as_arena_ref(),
            config,
            db,
        )
    }
}

impl<'a> IsVdLeanTranspilationInput<'a> for LxDocumentInput<'a> {
    type VdLeanTranspilationOutput = LnItemDefnIdxRange;
}

impl<'a> IsVdLeanTranspilationInput<'a> for LxDocumentBodyInput<'a> {
    type VdLeanTranspilationOutput = LnItemDefnIdxRange;
}

impl<'a> IsVdLeanTranspilationInput<'a> for LxPageInput<'a> {
    type VdLeanTranspilationOutput = LnItemDefnIdxRange;
}

impl<'a> IsVdLeanTranspilationInput<'a> for LxFormulaInput<'a> {
    type VdLeanTranspilationOutput = LnMirExprIdx;
}

impl<'a> IsVdLeanTranspilationOutput for LnItemDefnIdxRange {
    fn show_display_tree(self, builder: &LnMirExprDisplayTreeBuilder) -> String {
        DisplayTree::show_trees(&builder.render_defns(self), &Default::default())
    }

    fn show_fmt(self, formatter: &mut LnMirExprFormatter) {
        formatter.format_defns(self);
    }
}

impl<'a> IsVdLeanTranspilationOutput for LnMirExprIdx {
    fn show_display_tree(self, builder: &LnMirExprDisplayTreeBuilder) -> String {
        builder.render_expr(self).show(&Default::default())
    }

    fn show_fmt(self, formatter: &mut LnMirExprFormatter) {
        formatter.format_expr_ext(self);
    }
}
