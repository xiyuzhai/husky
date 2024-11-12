use super::*;

pub(super) fn update_pre_asts_by_new_asts(
    pre_asts: Seq<Option<PreAst>>,
    new_asts: Seq<Option<AstData>>,
) -> Seq<Option<PreAst>> {
    update_pre_ast_by_new_ast.apply(pre_asts, new_asts)
}

fn update_pre_ast_by_new_ast(pre_ast: Option<PreAst>, new_ast: Option<AstData>) -> Option<PreAst> {
    new_ast.map(PreAst::Ast).or(pre_ast)
}
