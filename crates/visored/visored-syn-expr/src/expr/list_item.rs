use super::*;
use latex_ast::ast::LxAstIdx;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdSynSeparatedListItem {
    syn_expr_idx: VdSynExprIdx,
    separator_latex_ast_idx: Option<LxAstIdx>,
}

impl VdSynSeparatedListItem {
    pub(crate) fn new(
        syn_expr_idx: VdSynExprIdx,
        separator_latex_ast_idx: Option<LxAstIdx>,
    ) -> Self {
        Self {
            syn_expr_idx,
            separator_latex_ast_idx,
        }
    }

    pub fn syn_expr_idx(self) -> VdSynExprIdx {
        self.syn_expr_idx
    }

    pub fn separator_latex_ast_idx(self) -> Option<LxAstIdx> {
        self.separator_latex_ast_idx
    }
}
