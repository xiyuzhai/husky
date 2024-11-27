pub mod props_ty_variant;
pub mod tuple_ty_variant;
pub mod unit_ty_variant;

use self::props_ty_variant::*;
use self::tuple_ty_variant::*;
use self::unit_ty_variant::*;
use super::*;
use husky_entity_path::path::ty_variant::TypeVariantPath;
use husky_entity_tree::node::ty_variant::TypeVariantSynNodePath;
use husky_token_data::Punctuation;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeVariantSynNodeDecl {
    Props(TypePropsVariantSynNodeDecl),
    Unit(TypeUnitVariantSynNodeDecl),
    Tuple(TypeTupleVariantSynNodeDecl),
}

impl TypeVariantSynNodeDecl {
    pub fn syn_node_path(self, db: &::salsa::Db) -> TypeVariantSynNodePath {
        match self {
            TypeVariantSynNodeDecl::Props(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeVariantSynNodeDecl::Unit(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeVariantSynNodeDecl::Tuple(syn_node_decl) => syn_node_decl.syn_node_path(db),
        }
    }
    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeVariantSynNodeDecl::Props(slf) => slf.syn_expr_region(db),
            TypeVariantSynNodeDecl::Unit(slf) => slf.syn_expr_region(db),
            TypeVariantSynNodeDecl::Tuple(slf) => slf.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            TypeVariantSynNodeDecl::Unit(slf) => slf.errors(db),
            TypeVariantSynNodeDecl::Props(slf) => slf.errors(db),
            TypeVariantSynNodeDecl::Tuple(slf) => slf.errors(db),
        }
    }
}

impl HasSynNodeDecl for TypeVariantSynNodePath {
    type NodeDecl = TypeVariantSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        ty_variant_syn_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_variant_syn_node_decl(
    db: &::salsa::Db,
    syn_node_path: TypeVariantSynNodePath,
) -> TypeVariantSynNodeDecl {
    ItemSynNodeDeclParser::new(db, syn_node_path.into()).parse_ty_variant_syn_node_decl()
}

impl<'a> ItemSynNodeDeclParser<'a> {
    fn parse_ty_variant_syn_node_decl(&self) -> TypeVariantSynNodeDecl {
        use parsec::HasStreamState;
        let db = self.db();
        let ItemSynNodePath::TypeVariant(_, syn_node_path) = self.syn_node_path() else {
            unreachable!()
        };
        let mut parser = self.expr_parser(
            Some(
                syn_node_path
                    .data(db)
                    .parent_ty_node_path
                    .syn_node_decl(db)
                    .syn_expr_region(db),
            ),
            AllowSelfType::True,
            AllowSelfValue::False,
            None,
        );
        let state = parser.state();
        match parser.next() {
            Some(TokenData::Punctuation(Punctuation::LPAR)) => {
                let fields = parser.try_parse();
                let rpar = parser.try_parse();
                TypeTupleVariantSynNodeDecl::new(
                    db,
                    syn_node_path,
                    state.next_regional_token_idx(),
                    fields,
                    rpar,
                    parser.finish(),
                )
                .into()
            }
            Some(TokenData::Punctuation(Punctuation::INLINE_LCURL)) => {
                let field_comma_list = parser.try_parse();
                let rcurl = parser.try_parse();
                TypePropsVariantSynNodeDecl::new(
                    db,
                    syn_node_path,
                    state.next_regional_token_idx(),
                    field_comma_list,
                    rcurl,
                    parser.finish(),
                )
                .into()
            }
            None => TypeUnitVariantSynNodeDecl::new(db, syn_node_path, parser.finish()).into(),
            other => {
                use husky_print_utils::p;
                p!(other);
                todo!()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeVariantSynDecl {
    Unit(TypeUnitVariantSynDecl),
    Props(TypePropsVariantSynDecl),
    Tuple(TypeTupleVariantSynDecl),
}

/// # constructor
impl TypeVariantSynDecl {
    fn from_node(
        db: &::salsa::Db,
        path: TypeVariantPath,
        syn_node_decl: TypeVariantSynNodeDecl,
    ) -> SynDeclResult<Self> {
        Ok(match syn_node_decl {
            TypeVariantSynNodeDecl::Props(syn_node_decl) => {
                TypePropsVariantSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeVariantSynNodeDecl::Unit(syn_node_decl) => {
                TypeUnitVariantSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeVariantSynNodeDecl::Tuple(syn_node_decl) => {
                TypeTupleVariantSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
        })
    }
}

/// # getters
impl TypeVariantSynDecl {
    pub fn path(self, db: &::salsa::Db) -> TypeVariantPath {
        match self {
            TypeVariantSynDecl::Unit(slf) => slf.path(db),
            TypeVariantSynDecl::Props(slf) => slf.path(db),
            TypeVariantSynDecl::Tuple(slf) => slf.path(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeVariantSynDecl::Unit(slf) => slf.syn_expr_region(db),
            TypeVariantSynDecl::Props(slf) => slf.syn_expr_region(db),
            TypeVariantSynDecl::Tuple(slf) => slf.syn_expr_region(db),
        }
    }
}

impl HasSynDecl for TypeVariantPath {
    type Decl = TypeVariantSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        ty_variant_syn_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_variant_syn_decl(
    db: &::salsa::Db,
    path: TypeVariantPath,
) -> SynDeclResult<TypeVariantSynDecl> {
    let syn_node_decl = path.syn_node_path(db).syn_node_decl(db);
    TypeVariantSynDecl::from_node(db, path, syn_node_decl)
}
