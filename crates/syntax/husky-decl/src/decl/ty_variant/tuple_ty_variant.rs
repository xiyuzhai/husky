use super::*;
use husky_expr::ExprIdx;
use parsec::{SeparatedSmallList, TryParseFromStream};

// todo: GADT
#[salsa::tracked(db = DeclDb, jar = DeclJar)]
pub struct TupleTypeVariantNodeDecl {
    #[id]
    pub node_path: TypeVariantNodePath,
    pub ast_idx: AstIdx,
    lpar_token_idx: TokenIdx,
    #[return_ref]
    field_comma_list:
        DeclExprResult<SeparatedSmallList<TupleFieldDeclPattern, CommaToken, 4, DeclExprError>>,
    #[return_ref]
    rpar: DeclExprResult<TupleTypeVariantRightParenthesisToken>,
    pub expr_region: ExprRegion,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TupleTypeVariantRightParenthesisToken(RightParenthesisToken);

impl<'a, 'b> TryParseFromStream<ExprParseContext<'a, 'b>>
    for TupleTypeVariantRightParenthesisToken
{
    type Error = DeclExprError;

    fn try_parse_from_stream(sp: &mut ExprParseContext) -> Result<Self, Self::Error> {
        // todo: enrich this
        // consider unexpected
        // maybe sp.skip_exprs_until_next_right_parenthesis
        let rpar = sp.try_parse_expected(
            OriginalDeclExprError::ExpectedRightParenthesisInTupleStructFieldTypeList,
        )?;
        Ok(Self(rpar))
    }
}

#[salsa::tracked(db = DeclDb, jar = DeclJar)]
pub struct TupleTypeVariantDecl {
    #[id]
    pub path: TypeVariantPath,
    pub fields: SmallVec<[TupleFieldDeclPattern; 4]>,
    pub expr_region: ExprRegion,
}

impl TupleTypeVariantDecl {
    pub(super) fn from_node_decl(
        db: &dyn DeclDb,
        path: TypeVariantPath,
        node_decl: TupleTypeVariantNodeDecl,
    ) -> DeclResult<Self> {
        let fields = SmallVec::from(node_decl.field_comma_list(db).as_ref()?.elements());
        Ok(Self::new(db, path, fields, node_decl.expr_region(db)))
    }
}