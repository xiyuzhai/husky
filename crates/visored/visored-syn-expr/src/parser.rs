// TODO: maybe move this under expr
mod accept;
mod debug;
mod disambiguate;
mod env;
mod expr_stack;
pub(crate) mod incomplete_expr;
mod utils;

use expr::VdSynExprIdx;
use latex_ast::ast::math::{LxMathAstIdx, LxMathAstIdxRange};
use range::VdSynExprTokenIdxRange;
use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};

use self::expr_stack::VdSynExprStack;
use crate::builder::VdSynExprBuilder;
use crate::*;

pub struct VdSynExprParser<'a, 'db> {
    builder: &'a mut VdSynExprBuilder<'db>,
    stack: VdSynExprStack,
}

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    fn new(builder: &'a mut VdSynExprBuilder<'db>) -> Self {
        Self {
            builder,
            stack: Default::default(),
        }
    }
}

impl<'db> VdSynExprBuilder<'db> {
    pub fn parser(&mut self) -> VdSynExprParser<'_, 'db> {
        VdSynExprParser::new(self)
    }
}

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub fn parse_asts(mut self, asts: LxMathAstIdxRange) -> VdSynExprIdx {
        let mut next = asts.start();
        let end = asts.end();
        while next < end {
            self.parse_ast(&mut next, end);
        }
        self.reduce(VdPrecedenceRange::Any, None);
        let Self { builder, stack } = self;
        builder.alloc_expr(stack.finish())
    }

    fn parse_ast(&mut self, next: &mut LxMathAstIdx, end: LxMathAstIdx) {
        let range = self.builder.ast_token_idx_range_map()[*next];
        let preceding_space_annotation = self
            .builder
            .annotations()
            .preceding_space_annotation(range.start());
        let token = self.resolve_token(next, end);
        let range = range.join(self.builder.ast_token_idx_range_map()[*next - 1]);
        self.accept_ast(preceding_space_annotation, range, token);
    }
}
