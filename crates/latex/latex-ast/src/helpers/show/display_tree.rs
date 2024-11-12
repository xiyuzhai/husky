use crate::{
    ast::{
        math::{
            helpers::LxMathAstChild, LxMathAstIdx, LxMathAstIdxRange, LxMathCommandArgument,
            LxMathCommandArgumentData,
        },
        rose::{helpers::LxRoseAstChild, LxRoseAstIdx},
        LxAstArenaRef, LxAstIdx, LxAstIdxRange,
    },
    range::LxAstTokenIdxRangeMap,
};
use husky_tree_utils::display::DisplayTree;
use latex_token::storage::LxTokenStorage;

pub struct LxAstDisplayTreeBuilder<'a> {
    db: &'a salsa::Db,
    input: &'a str,
    ast_arena: LxAstArenaRef<'a>,
    ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
    token_storage: &'a LxTokenStorage,
}

/// # construction
impl<'a> LxAstDisplayTreeBuilder<'a> {
    pub fn new(
        db: &'a salsa::Db,
        input: &'a str,
        token_storage: &'a LxTokenStorage,
        ast_arena: LxAstArenaRef<'a>,
        ast_token_idx_range_map: &'a LxAstTokenIdxRangeMap,
    ) -> Self {
        Self {
            db,
            input,
            ast_arena,
            ast_token_idx_range_map,
            token_storage,
        }
    }
}

/// # actions
impl<'a> LxAstDisplayTreeBuilder<'a> {
    pub fn render_all(&self, asts: LxAstIdxRange) -> DisplayTree {
        DisplayTree::new(self.input.to_string(), self.render_asts(asts))
    }

    pub fn render_asts(&self, asts: LxAstIdxRange) -> Vec<DisplayTree> {
        match asts {
            LxAstIdxRange::Math(range) => self.render_math_asts(range),
            LxAstIdxRange::Rose(range) => self.render_rose_asts(range),
        }
    }

    fn render_math_asts(&self, asts: impl IntoIterator<Item = LxMathAstIdx>) -> Vec<DisplayTree> {
        asts.into_iter()
            .map(|ast| self.render_math_ast(ast))
            .collect()
    }

    fn render_rose_asts(&self, asts: impl IntoIterator<Item = LxRoseAstIdx>) -> Vec<DisplayTree> {
        asts.into_iter()
            .map(|ast| self.render_rose_ast(ast))
            .collect()
    }

    fn render_math_ast(&self, ast: LxMathAstIdx) -> DisplayTree {
        let ast_token_idx_range = self.ast_token_idx_range_map[ast];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(ast_token_idx_range);
        let value = self.input[offset_range].to_string();
        DisplayTree::new(
            value,
            self.render_math_children(self.ast_arena.math()[ast].children()),
        )
    }

    fn render_math_children(
        &self,
        children: impl IntoIterator<Item = LxMathAstChild>,
    ) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| self.render_math_child(child))
            .collect()
    }

    fn render_math_child(&self, child: LxMathAstChild) -> DisplayTree {
        match child {
            LxMathAstChild::Ast(ast) => self.render_math_ast(ast),
            LxMathAstChild::CommandArgument(argument) => {
                self.render_math_command_argument(argument)
            }
        }
    }

    fn render_math_command_argument(&self, argument: LxMathCommandArgument) -> DisplayTree {
        match argument.data() {
            LxMathCommandArgumentData::Math(range) => {
                let value = if range.is_empty() {
                    "".to_string()
                } else {
                    let range = self.ast_token_idx_range_map[range.start()]
                        .join(self.ast_token_idx_range_map[range.last().unwrap()]);
                    self.input[self.token_storage.token_idx_range_offset_range(range)].to_string()
                };
                let grandchildren = self.render_math_asts(range);
                DisplayTree::new(value, grandchildren)
            }
            LxMathCommandArgumentData::Rose(range) => todo!(),
            LxMathCommandArgumentData::Letter(_, _) => todo!(),
        }
    }

    fn render_rose_ast(&self, ast: LxRoseAstIdx) -> DisplayTree {
        let ast_token_idx_range = self.ast_token_idx_range_map[ast];
        let offset_range = self
            .token_storage
            .token_idx_range_offset_range(ast_token_idx_range);
        let value = self.input[offset_range].to_string();
        DisplayTree::new(
            value,
            self.render_rose_children(self.ast_arena.rose()[ast].children()),
        )
    }

    fn render_rose_children(
        &self,
        children: impl IntoIterator<Item = LxRoseAstChild>,
    ) -> Vec<DisplayTree> {
        children
            .into_iter()
            .map(|child| self.render_rose_child(child))
            .collect()
    }

    fn render_rose_child(&self, child: LxRoseAstChild) -> DisplayTree {
        match child {
            LxRoseAstChild::RoseAst(ast) => self.render_rose_ast(ast),
            LxRoseAstChild::MathAst(ast) => self.render_math_ast(ast),
        }
    }
}
