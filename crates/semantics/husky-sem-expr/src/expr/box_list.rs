use super::*;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_new_list_expr_ty(
        &mut self,
        expr_idx: SynExprIdx,
        items: SynExprIdxRange,
    ) -> SemExprTypeResult<FlyTerm> {
        todo!()
        // let element_ty: FlyTerm = self
        //     .fly_term_region
        //     .new_implicit_symbol(expr_idx, ImplicitSymbolVariant::ImplicitType)
        //     .into();
        // for item in items {
        //     self.infer_new_expr_ty_discarded(
        //         item,
        //         ExpectImplicitlyConvertible::new_transient(element_ty),
        //     );
        // }
        // Ok(self.new_ty_ontology_application(
        //     expr_idx,
        //     self.item_path_menu.vec_ty_path(),
        //     smallvec![element_ty],
        // ))
    }
}
