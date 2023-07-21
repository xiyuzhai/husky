mod props_ty_variant;
mod tuple_ty_variant;
mod unit_ty_variant;

pub use self::props_ty_variant::*;
pub use self::tuple_ty_variant::*;
pub use self::unit_ty_variant::*;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::derive_debug_with_db(db = DeclDb)]
#[enum_class::from_variants]
pub enum TypeVariantNodeDecl {
    Props(PropsTypeVariantNodeDecl),
    Unit(UnitTypeVariantNodeDecl),
    Tuple(TupleTypeVariantNodeDecl),
}

impl TypeVariantNodeDecl {
    pub fn node_path(self, db: &dyn DeclDb) -> TypeVariantSynNodePath {
        match self {
            TypeVariantNodeDecl::Props(node_decl) => node_decl.node_path(db),
            TypeVariantNodeDecl::Unit(node_decl) => node_decl.node_path(db),
            TypeVariantNodeDecl::Tuple(node_decl) => node_decl.node_path(db),
        }
    }

    pub fn ast_idx(self, db: &dyn DeclDb) -> AstIdx {
        match self {
            TypeVariantNodeDecl::Props(node_decl) => node_decl.ast_idx(db),
            TypeVariantNodeDecl::Unit(node_decl) => node_decl.ast_idx(db),
            TypeVariantNodeDecl::Tuple(node_decl) => node_decl.ast_idx(db),
        }
    }

    pub fn errors(self, db: &dyn DeclDb) -> NodeDeclErrorRefs {
        match self {
            TypeVariantNodeDecl::Props(_) => todo!(),
            TypeVariantNodeDecl::Unit(_) => todo!(),
            TypeVariantNodeDecl::Tuple(_) => todo!(),
        }
    }
}

impl HasNodeDecl for TypeVariantSynNodePath {
    type NodeDecl = TypeVariantNodeDecl;

    fn node_decl<'a>(self, db: &'a dyn DeclDb) -> Self::NodeDecl {
        ty_variant_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_variant_node_decl(
    db: &dyn DeclDb,
    node_path: TypeVariantSynNodePath,
) -> TypeVariantNodeDecl {
    DeclParser::new(db, node_path.module_path(db)).parse_ty_variant_node_decl(node_path)
}

impl<'a> DeclParser<'a> {
    fn parse_ty_variant_node_decl(&self, node_path: TypeVariantSynNodePath) -> TypeVariantNodeDecl {
        let db = self.db();
        let node = node_path.node(db);
        let ast_idx = node.ast_idx(db);
        let Ast::TypeVariant {
            token_group_idx,
            vertical_token,
            ident_token,
            state_after,
            ..
        } = self.ast_sheet()[ast_idx] else {
            unreachable!()
        };
        let mut parser = self.expr_parser(
            node_path,
            Some(
                node_path
                    .parent_ty_node_path(db)
                    .node_decl(db)
                    .expr_region(db),
            ),
            AllowSelfType::True,
            AllowSelfValue::False,
        );
        let mut ctx = parser.ctx(None, token_group_idx, Some(state_after));
        let state = ctx.save_state();
        match ctx.next() {
            Some(Token::Punctuation(Punctuation::LPAR)) => {
                let field_comma_list = ctx.try_parse();
                let rpar = ctx.try_parse();
                TupleTypeVariantNodeDecl::new(
                    db,
                    node_path,
                    ast_idx,
                    state.next_token_idx(),
                    field_comma_list,
                    rpar,
                    parser.finish(),
                )
                .into()
            }
            Some(Token::Punctuation(Punctuation::LCURL)) => todo!(),
            None => UnitTypeVariantNodeDecl::new(db, node_path, ast_idx, parser.finish()).into(),
            _ => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::derive_debug_with_db(db = DeclDb)]
#[enum_class::from_variants]
pub enum TypeVariantDecl {
    Props(PropsTypeVariantDecl),
    Unit(UnitTypeVariantDecl),
    Tuple(TupleTypeVariantDecl),
}

impl TypeVariantDecl {
    fn from_node_decl(
        db: &dyn DeclDb,
        path: TypeVariantPath,
        node_decl: TypeVariantNodeDecl,
    ) -> DeclResult<Self> {
        Ok(match node_decl {
            TypeVariantNodeDecl::Props(node_decl) => {
                PropsTypeVariantDecl::from_node_decl(db, path, node_decl)?.into()
            }
            TypeVariantNodeDecl::Unit(node_decl) => {
                UnitTypeVariantDecl::from_node_decl(db, path, node_decl)?.into()
            }
            TypeVariantNodeDecl::Tuple(node_decl) => {
                TupleTypeVariantDecl::from_node_decl(db, path, node_decl)?.into()
            }
        })
    }

    pub fn path(self, db: &dyn DeclDb) -> TypeVariantPath {
        match self {
            TypeVariantDecl::Props(_) => todo!(),
            TypeVariantDecl::Unit(_) => todo!(),
            TypeVariantDecl::Tuple(_) => todo!(),
        }
    }

    pub(crate) fn ast_idx(self, _db: &dyn DeclDb) -> AstIdx {
        todo!()
    }
}

impl HasDecl for TypeVariantPath {
    type Decl = TypeVariantDecl;

    fn decl(self, db: &dyn DeclDb) -> DeclResult<Self::Decl> {
        ty_variant_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_variant_decl(
    db: &dyn DeclDb,
    path: TypeVariantPath,
) -> DeclResult<TypeVariantDecl> {
    let node_decl = path.syn_node_path(db).node_decl(db);
    TypeVariantDecl::from_node_decl(db, path, node_decl)
}