pub mod r#enum;
pub mod r#extern;
pub mod inductive;
pub mod props_struct;
pub mod structure;
pub mod tuple_struct;
pub mod union;
pub mod unit_struct;

use self::inductive::*;
use self::props_struct::*;
use self::r#enum::*;
use self::r#extern::*;
use self::structure::*;
use self::tuple_struct::*;
use self::union::*;
use self::unit_struct::*;
use super::*;
use husky_entity_kind::TypeKind;
use husky_entity_path::path::major_item::ty::TypePath;
use husky_entity_tree::node::major_item::ty::TypeSynNodePath;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeSynNodeDecl {
    Enum(EnumSynNodeDecl),
    PropsStruct(PropsStructSynNodeDecl),
    UnitStruct(UnitStructSynNodeDecl),
    TupleStruct(TupleStructSynNodeDecl),
    Inductive(InductiveSynNodeDecl),
    Structure(StructureSynNodeDecl),
    Extern(ExternSynNodeDecl),
    Union(UnionSynNodeDecl),
}

impl TypeSynNodeDecl {
    pub fn syn_node_path(self, db: &::salsa::Db) -> TypeSynNodePath {
        match self {
            TypeSynNodeDecl::Enum(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::Inductive(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::UnitStruct(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::PropsStruct(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::TupleStruct(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::Structure(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::Extern(syn_node_decl) => syn_node_decl.syn_node_path(db),
            TypeSynNodeDecl::Union(syn_node_decl) => syn_node_decl.syn_node_path(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeSynNodeDecl::Enum(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::UnitStruct(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::TupleStruct(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::PropsStruct(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::Inductive(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::Structure(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::Extern(syn_node_decl) => syn_node_decl.syn_expr_region(db),
            TypeSynNodeDecl::Union(syn_node_decl) => syn_node_decl.syn_expr_region(db),
        }
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        match self {
            TypeSynNodeDecl::Enum(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::PropsStruct(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::UnitStruct(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::TupleStruct(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::Inductive(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::Structure(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::Extern(syn_node_decl) => syn_node_decl.errors(db),
            TypeSynNodeDecl::Union(syn_node_decl) => syn_node_decl.errors(db),
        }
    }
}

impl HasSynNodeDecl for TypeSynNodePath {
    type NodeDecl = TypeSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        ty_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_node_decl(db: &::salsa::Db, syn_node_path: TypeSynNodePath) -> TypeSynNodeDecl {
    ItemSynNodeDeclParser::new(db, syn_node_path.into()).parse_ty_node_decl(syn_node_path)
}

impl<'a> ItemSynNodeDeclParser<'a> {
    fn parse_ty_node_decl(&self, _syn_node_path: TypeSynNodePath) -> TypeSynNodeDecl {
        let ItemSynNodePath::MajorItem(MajorItemSynNodePath::Type(syn_node_path)) =
            self.syn_node_path()
        else {
            unreachable!()
        };
        match syn_node_path.ty_kind(self.db()) {
            TypeKind::Enum => self.parse_enum_ty_node_decl(syn_node_path).into(),
            TypeKind::Inductive => self.parse_inductive_ty_node_decl(syn_node_path).into(),
            TypeKind::Record => todo!(),
            TypeKind::Struct => self.parse_struct_ty_node_decl(syn_node_path),
            TypeKind::Structure => self.parse_structure_ty_node_decl(syn_node_path),
            TypeKind::Extern => self.parse_extern_ty_node_decl(syn_node_path).into(),
        }
    }
}

impl<'a> ItemSynNodeDeclParser<'a> {
    pub(super) fn parse_struct_ty_node_decl(
        &self,
        syn_node_path: TypeSynNodePath,
    ) -> TypeSynNodeDecl {
        let db = self.db();
        let mut parser = self.expr_parser(None, AllowSelfType::True, AllowSelfValue::False, None);
        let template_parameters = parser.try_parse_option();
        if let Some(lpar) = parser.try_parse_err_as_none::<LparRegionalToken>() {
            let field_comma_list = parser.try_parse();
            let rpar = parser.try_parse();
            TupleStructSynNodeDecl::new(
                db,
                syn_node_path,
                template_parameters,
                lpar,
                field_comma_list,
                rpar,
                parser.finish(),
            )
            .into()
        } else if let Some(semicolon) = parser.try_parse_err_as_none::<SemiColonRegionalToken>() {
            UnitStructSynNodeDecl::new(db, syn_node_path, template_parameters, parser.finish())
                .into()
        } else {
            let lcurl = parser.try_parse();
            let field_comma_list = parser.try_parse();
            let rcurl = parser.try_parse();
            PropsStructSynNodeDecl::new(
                db,
                syn_node_path,
                template_parameters,
                lcurl,
                field_comma_list,
                rcurl,
                parser.finish(),
            )
            .into()
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TypeSynDecl {
    Enum(EnumSynDecl),
    PropsStruct(PropsStructSynDecl),
    UnitStruct(UnitStructSynDecl),
    TupleStruct(TupleStructSynDecl),
    Inductive(InductiveSynDecl),
    Structure(StructureSynDecl),
    Extern(ExternSynDecl),
    Union(UnionSynDecl),
}

impl TypeSynDecl {
    pub fn path(self, db: &::salsa::Db) -> TypePath {
        match self {
            TypeSynDecl::Enum(decl) => decl.path(db),
            TypeSynDecl::Inductive(decl) => decl.path(db),
            TypeSynDecl::UnitStruct(decl) => decl.path(db),
            TypeSynDecl::PropsStruct(decl) => decl.path(db),
            TypeSynDecl::TupleStruct(decl) => decl.path(db),
            TypeSynDecl::Structure(decl) => decl.path(db),
            TypeSynDecl::Extern(decl) => decl.path(db),
            TypeSynDecl::Union(decl) => decl.path(db),
        }
    }

    pub fn template_parameters<'a>(self, db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        match self {
            TypeSynDecl::Enum(decl) => decl.template_parameters(db),
            TypeSynDecl::UnitStruct(decl) => decl.template_parameters(db),
            TypeSynDecl::TupleStruct(decl) => decl.template_parameters(db),
            TypeSynDecl::PropsStruct(decl) => decl.template_parameters(db),
            TypeSynDecl::Inductive(decl) => decl.template_parameters(db),
            TypeSynDecl::Structure(decl) => decl.template_parameters(db),
            TypeSynDecl::Extern(decl) => decl.template_parameters(db),
            TypeSynDecl::Union(decl) => decl.template_parameters(db),
        }
    }

    pub fn syn_expr_region(self, db: &::salsa::Db) -> SynExprRegion {
        match self {
            TypeSynDecl::Enum(decl) => decl.syn_expr_region(db),
            TypeSynDecl::UnitStruct(decl) => decl.syn_expr_region(db),
            TypeSynDecl::TupleStruct(decl) => decl.syn_expr_region(db),
            TypeSynDecl::PropsStruct(decl) => decl.syn_expr_region(db),
            TypeSynDecl::Inductive(decl) => decl.syn_expr_region(db),
            TypeSynDecl::Structure(decl) => decl.syn_expr_region(db),
            TypeSynDecl::Extern(decl) => decl.syn_expr_region(db),
            TypeSynDecl::Union(decl) => decl.syn_expr_region(db),
        }
    }

    #[inline(always)]
    fn from_node(
        db: &::salsa::Db,
        path: TypePath,
        syn_node_decl: TypeSynNodeDecl,
    ) -> SynDeclResult<Self> {
        Ok(match syn_node_decl {
            TypeSynNodeDecl::Enum(syn_node_decl) => {
                EnumSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::PropsStruct(syn_node_decl) => {
                PropsStructSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::UnitStruct(syn_node_decl) => {
                UnitStructSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::TupleStruct(syn_node_decl) => {
                TupleStructSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::Inductive(syn_node_decl) => {
                InductiveSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::Structure(syn_node_decl) => {
                StructureSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::Extern(syn_node_decl) => {
                ExternSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
            TypeSynNodeDecl::Union(syn_node_decl) => {
                UnionSynDecl::from_node(db, path, syn_node_decl)?.into()
            }
        })
    }
}

impl HasSynDecl for TypePath {
    type Decl = TypeSynDecl;

    #[inline(always)]
    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        ty_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn ty_decl(db: &::salsa::Db, path: TypePath) -> SynDeclResult<TypeSynDecl> {
    TypeSynDecl::from_node(db, path, path.syn_node_path(db).syn_node_decl(db))
}

#[test]
fn ty_decl_works() {
    use husky_entity_path::menu::item_path_menu;

    let db = DB::default();
    let db = &*db;
    let toolchain = db.dev_toolchain().unwrap();
    let menu = item_path_menu(db, toolchain);
    assert!(menu.never_ty_path().syn_decl(db).is_ok());
}
