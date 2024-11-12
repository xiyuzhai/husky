use super::*;

pub(super) fn allocate_asts_and_update_parents(
    asts: Seq<Option<Ast>>,
    new_asts: Seq<Option<AstData>>,
    new_parents: Seq<Option<Idx>>,
) -> Seq<Option<Ast>> {
    allocate_ast.apply(asts, new_asts, new_parents)
}

fn allocate_ast(
    ast: Option<Ast>,
    new_ast: Option<AstData>,
    new_parent: Option<Idx>,
) -> Option<Ast> {
    match new_ast {
        Some(data) => {
            debug_assert!(ast.is_none());
            debug_assert!(new_parent.is_none());
            Some(Ast { parent: None, data })
        }
        None => match new_parent {
            Some(new_parent) => {
                let Some(ast) = ast else { unreachable!() };
                debug_assert!(ast.parent.is_none());
                Some(Ast {
                    parent: Some(new_parent),
                    data: ast.data,
                })
            }
            None => ast,
        },
    }
}
