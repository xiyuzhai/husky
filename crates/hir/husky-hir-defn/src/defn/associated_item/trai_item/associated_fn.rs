use super::*;

#[salsa::interned(db = HirDefnDb, jar = HirDefnJar, constructor = new_inner)]
pub struct TraitAssociatedFnHirDefn {
    pub syn_node_path: TraitItemPath,
    pub hir_decl: TraitAssociatedFnHirDecl,
    pub hir_expr_region: HirEagerExprRegion,
}

impl TraitAssociatedFnHirDefn {
    pub(super) fn new(
        _db: &dyn HirDefnDb,
        _path: TraitItemPath,
        _hir_decl: TraitAssociatedFnHirDecl,
    ) -> TraitAssociatedFnHirDefn {
        todo!()
        // let syn_node_path = hir_decl.syn_node_path(db);
        // let mut parser = expr_parser(
        //     db,
        //     syn_node_path,
        //     Some(hir_decl.hir_expr_region(db)),
        //     AllowSelfType::True,
        //     AllowSelfValue::True,
        // );
        // let ast_idx = hir_decl.ast_idx(db);
        // let body = match parser.ast_sheet()[ast_idx] {
        //     Ast::Defn {
        //         block: DefnBlock::AssociatedItem { body },
        //         ..
        //     } => body.map(|body| parser.parse_block_expr(body)),
        //     _ => unreachable!(),
        // };
        // TraitForTypeMethodFnDefn::new(db, syn_node_path, hir_decl, body, parser.finish())
    }
}