use crate::{
    ast::{
        lisp::LxLispAstIdxRange,
        math::{LxMathAstIdx, LxMathAstIdxRange},
        parse_latex_input_into_asts,
        root::LxRootAstIdxRange,
        rose::LxRoseAstIdxRange,
        LxAstArena, LxAstIdxRange,
    },
    helpers::show::display_tree::LxAstDisplayTreeBuilder,
    parser::LxAstParser,
    range::{calc_ast_token_idx_range_map, LxAstTokenIdxRangeMap},
};
use husky_tree_utils::display::DisplayTree;
use latex_command::signature::table::LxCommandSignatureTable;
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_prelude::{
    helper::tracker::{
        IsLxInput, LxDocumentBodyInput, LxDocumentInput, LxFormulaInput, LxLispInput, LxPageInput,
    },
    mode::LxMode,
};
use latex_token::{lane::LxTokenLane, storage::LxTokenStorage};

#[derive(Debug)]
pub struct LxAstTracker<'a, Input: IsLxAstInput<'a>> {
    pub command_signature_table: LxCommandSignatureTable,
    pub input: Input,
    pub token_storage: LxTokenStorage,
    pub ast_arena: LxAstArena,
    pub ast_token_idx_range_map: LxAstTokenIdxRangeMap,
    pub output: Input::LxAstOutput,
}

pub trait IsLxAstInput<'a>: IsLxInput<'a> {
    type LxAstOutput: std::fmt::Debug + Copy;

    fn parse(parser: LxAstParser) -> Self::LxAstOutput;
    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String;
}

impl<'a, Input: IsLxAstInput<'a>> LxAstTracker<'a, Input> {
    pub fn new(input: Input) -> Self {
        let mut ast_arena = LxAstArena::default();
        let mut token_storage = LxTokenStorage::default();
        let command_signature_table = LxCommandSignatureTable::new_from_lp_csv_file_paths(
            &input.latex_complete_commands_path(),
        );
        let environment_signature_table = LxEnvironmentSignatureTable::new_default();
        let mut parser = LxAstParser::new(
            &command_signature_table,
            &environment_signature_table,
            input.content(),
            LxTokenLane::Main,
            input.root_mode(),
            &mut token_storage,
            &mut ast_arena,
        );
        let output = Input::parse(parser);
        let ast_token_idx_range_map = calc_ast_token_idx_range_map(&ast_arena);
        Self {
            command_signature_table,
            input,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            output,
        }
    }
}

impl<'a, Input: IsLxAstInput<'a>> LxAstTracker<'a, Input> {
    fn display_tree_builder<'b>(&'b self) -> LxAstDisplayTreeBuilder<'b> {
        LxAstDisplayTreeBuilder::new(
            self.input.content(),
            &self.token_storage,
            self.ast_arena.as_arena_ref(),
            &self.ast_token_idx_range_map,
        )
    }

    pub fn show(&self) -> String {
        let display_tree_builder = self.display_tree_builder();
        Input::show_lx_ast_output(self.output, display_tree_builder)
    }
}

impl<'a> IsLxAstInput<'a> for LxDocumentInput<'a> {
    type LxAstOutput = LxRootAstIdxRange;

    fn parse(mut parser: LxAstParser) -> Self::LxAstOutput {
        parser.parse_root_asts()
    }

    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String {
        format!(
            "{}",
            DisplayTree::show_trees(&builder.render_root_asts(output), &Default::default(),)
        )
    }
}

impl<'a> IsLxAstInput<'a> for LxDocumentBodyInput<'a> {
    type LxAstOutput = LxRoseAstIdxRange;

    fn parse(mut parser: LxAstParser) -> Self::LxAstOutput {
        parser.parse_rose_asts()
    }

    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String {
        format!(
            "{}",
            DisplayTree::show_trees(&builder.render_rose_asts(output), &Default::default(),)
        )
    }
}

impl<'a> IsLxAstInput<'a> for LxPageInput<'a> {
    type LxAstOutput = LxRoseAstIdxRange;

    fn parse(mut parser: LxAstParser) -> Self::LxAstOutput {
        parser.parse_rose_asts()
    }

    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String {
        format!(
            "{}",
            DisplayTree::show_trees(&builder.render_rose_asts(output), &Default::default(),)
        )
    }
}

impl<'a> IsLxAstInput<'a> for LxFormulaInput<'a> {
    type LxAstOutput = LxMathAstIdxRange;

    fn parse(mut parser: LxAstParser) -> Self::LxAstOutput {
        parser.parse_math_asts()
    }

    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String {
        format!(
            "{}",
            DisplayTree::show_trees(&builder.render_math_asts(output), &Default::default(),)
        )
    }
}

impl<'a> IsLxAstInput<'a> for LxLispInput<'a> {
    type LxAstOutput = LxLispAstIdxRange;

    fn parse(mut parser: LxAstParser) -> Self::LxAstOutput {
        parser.parse_lisp_asts()
    }

    fn show_lx_ast_output(output: Self::LxAstOutput, builder: LxAstDisplayTreeBuilder) -> String {
        format!(
            "{}",
            DisplayTree::show_trees(&builder.render_lisp_asts(output), &Default::default(),)
        )
    }
}
