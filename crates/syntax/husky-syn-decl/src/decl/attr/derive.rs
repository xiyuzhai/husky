use super::*;
use husky_entity_tree::node::attr::AttrSynNodePath;
use parsec::PunctuatedSmallList;

#[salsa::tracked(db = SynDeclDb, jar = SynDeclJar, constructor = new_inner)]
pub struct DeriveAttrSynNodeDecl {
    #[id]
    pub syn_node_path: AttrSynNodePath,
    pub pound_token: PoundRegionalToken,
    pub derive_token: IdentRegionalToken,
    #[return_ref]
    pub lpar_token: SynNodeDeclResult<LparRegionalToken>,
    #[return_ref]
    pub trais: SynNodeDeclResult<
        PunctuatedSmallList<TraitSyndicate, CommaRegionalToken, SynNodeDeclError, true, 8>,
    >,
    #[return_ref]
    pub rpar_token: SynNodeDeclResult<RparRegionalToken>,
    pub syn_expr_region: SynExprRegion,
}

/// # constructor

impl DeriveAttrSynNodeDecl {
    pub(super) fn new(db: &::salsa::Db, syn_node_path: AttrSynNodePath) -> Self {
        let parser_factory = ItemSynNodeDeclParser::new(db, syn_node_path.into());
        let mut parser = parser_factory.expr_parser(
            syn_node_path
                .parent_syn_node_path(db)
                .syn_node_decl(db)
                .syn_expr_region(db),
            AllowSelfType::True,
            AllowSelfValue::False,
            None,
        );
        let pound_token = parser
            .try_parse_option()
            .expect("should be guaranteed")
            .expect("should be guaranteed");
        let derive_token = parser
            .try_parse_option()
            .expect("should be guaranteed")
            .expect("should be guaranteed");
        let lpar_token =
            parser.try_parse_expected(OriginalSynNodeDeclError::ExpectedLeftDelimiterInDerive);
        let trais = parser.try_parse();
        let rpar_token =
            parser.try_parse_expected(OriginalSynNodeDeclError::ExpectedRightDelimiterInDerive);
        Self::new_inner(
            db,
            syn_node_path,
            pound_token,
            derive_token,
            lpar_token,
            trais,
            rpar_token,
            parser.finish(),
        )
    }
}

/// # getters

impl DeriveAttrSynNodeDecl {
    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        chain_as_ref_err_collect!(self.lpar_token(db), self.trais(db), self.rpar_token(db))
    }
}

#[salsa::tracked]
pub struct DeriveAttrSynDecl {
    #[id]
    pub path: AttrItemPath,
    #[return_ref]
    pub trais: SmallVec<[TraitSyndicate; 8]>,
    pub syn_expr_region: SynExprRegion,
}

impl DeriveAttrSynDecl {
    #[inline(always)]
    pub(super) fn from_node(
        db: &::salsa::Db,
        path: AttrItemPath,
        syn_node_decl: DeriveAttrSynNodeDecl,
    ) -> SynDeclResult<Self> {
        let trais = SmallVec::from(syn_node_decl.trais(db).as_ref()?.elements());
        let syn_expr_region = syn_node_decl.syn_expr_region(db);
        Ok(Self::new(db, path, trais, syn_expr_region))
    }
}
