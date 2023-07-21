use husky_print_utils::p;

use super::*;

#[salsa::tracked(db = DeclDb, jar = SynDeclJar)]
pub struct TraitForTypeAssociatedTypeNodeDecl {
    #[id]
    pub node_path: TraitForTypeItemSynNodePath,
    pub node: TraitForTypeItemNode,
    pub ast_idx: AstIdx,
    #[return_ref]
    pub generics: NodeDeclResult<Option<Generics>>,
    #[return_ref]
    pub eq_token: NodeDeclResult<EqToken>,
    // todo: change this to NodeDeclResult??
    pub ty_term_expr_idx: ExprIdx,
    pub expr_region: SynExprRegion,
}

impl TraitForTypeAssociatedTypeNodeDecl {
    pub fn errors(self, db: &dyn DeclDb) -> NodeDeclErrorRefs {
        // ad hoc
        Default::default()
    }
}

impl<'a> DeclParser<'a> {
    pub(super) fn parse_trai_for_ty_associated_ty_node_decl(
        &self,
        node_path: TraitForTypeItemSynNodePath,
        node: TraitForTypeItemNode,
        ast_idx: AstIdx,
        token_group_idx: TokenGroupIdx,
        saved_stream_state: TokenStreamState,
    ) -> TraitForTypeAssociatedTypeNodeDecl {
        let db = self.db();
        let impl_block_node_decl = node_path.impl_block(db).node_decl(db);
        let mut parser = self.expr_parser(
            node.node_path(db),
            Some(impl_block_node_decl.expr_region(db)),
            AllowSelfType::True,
            AllowSelfValue::False,
        );
        let mut ctx = parser.ctx(None, token_group_idx, saved_stream_state);
        let eq_token = ctx.try_parse_expected(OriginalNodeDeclError::ExpectedEqForAssociatedType);
        let ty_term_expr_idx = ctx.parse_expr_expected2(
            None,
            ExprRootKind::AssociatedTypeTerm,
            OriginalExprError::ExpectedTypeTermForAssociatedType,
        );
        let generics = ctx.try_parse_option();
        TraitForTypeAssociatedTypeNodeDecl::new(
            db,
            node.node_path(db),
            node,
            ast_idx,
            generics,
            eq_token,
            ty_term_expr_idx,
            parser.finish(),
        )
    }
}

#[salsa::tracked(db = DeclDb, jar = SynDeclJar)]
pub struct TraitForTypeAssociatedTypeDecl {
    #[id]
    pub path: TraitForTypeItemPath,
    #[return_ref]
    pub generic_parameters: ImplicitParameterDeclPatterns,
    pub ty_term_expr_idx: ExprIdx,
    pub expr_region: SynExprRegion,
}

impl TraitForTypeAssociatedTypeDecl {
    pub(super) fn from_node_decl(
        db: &dyn DeclDb,
        path: TraitForTypeItemPath,
        node_decl: TraitForTypeAssociatedTypeNodeDecl,
    ) -> DeclResult<Self> {
        let generic_parameters = node_decl
            .generics(db)
            .as_ref()?
            .as_ref()
            .map(|list| list.generic_parameters().to_smallvec())
            .unwrap_or_default();
        let expr_region = node_decl.expr_region(db);
        let ty_term_expr_idx = node_decl.ty_term_expr_idx(db);
        Ok(TraitForTypeAssociatedTypeDecl::new(
            db,
            path,
            generic_parameters,
            ty_term_expr_idx,
            expr_region,
        ))
    }
}