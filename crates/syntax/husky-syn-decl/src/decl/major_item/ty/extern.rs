use super::*;
#[cfg(test)]
use husky_entity_path::menu::item_path_menu;

#[salsa::tracked]
pub struct ExternSynNodeDecl {
    #[id]
    pub syn_node_path: TypeSynNodePath,
    #[return_ref]
    template_parameter_decl_list: SynNodeDeclResult<Option<SynTemplateParameterSyndicateList>>,
    pub syn_expr_region: SynExprRegion,
}

impl ExternSynNodeDecl {
    pub fn template_parameters<'a>(self, _db: &'a ::salsa::Db) -> &'a [TemplateSynParameterData] {
        todo!()
        // self.template_parameter_decl_list(db)
        //     .as_ref()
        //     .map(ImplicitParameterDeclList::template_parameters)
        //     .unwrap_or(&[])
    }

    pub fn errors(self, db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        SmallVec::from_iter(
            self.template_parameter_decl_list(db)
                .as_ref()
                .err()
                .into_iter(),
        )
    }
}

impl<'a> ItemSynNodeDeclParser<'a> {
    // get declaration from tokens
    pub(super) fn parse_extern_ty_node_decl(
        &self,
        syn_node_path: TypeSynNodePath,
    ) -> ExternSynNodeDecl {
        let mut parser = self.expr_parser(None, AllowSelfType::True, AllowSelfValue::False, None);
        let template_parameters = parser.try_parse_option();
        ExternSynNodeDecl::new(
            self.db(),
            syn_node_path,
            template_parameters,
            parser.finish(),
        )
    }
}

#[salsa::tracked(db = SynDeclDb, jar = SynDeclJar, constructor = new)]
pub struct ExternSynDecl {
    #[id]
    pub path: TypePath,
    #[return_ref]
    pub template_parameters: TemplateSynParametersData,
    pub syn_expr_region: SynExprRegion,
}

impl ExternSynDecl {
    #[inline(always)]
    pub(super) fn from_node(
        db: &::salsa::Db,
        path: TypePath,
        syn_node_decl: ExternSynNodeDecl,
    ) -> SynDeclResult<Self> {
        let template_parameters = syn_node_decl
            .template_parameter_decl_list(db)
            .as_ref()?
            .as_ref()
            .map(|list| {
                list.syn_template_parameter_obelisks()
                    .iter()
                    .map(Clone::clone)
                    .collect()
            })
            .unwrap_or_default();
        let syn_expr_region = syn_node_decl.syn_expr_region(db);
        Ok(Self::new(db, path, template_parameters, syn_expr_region))
    }
}

#[test]
fn extern_ty_decl_works() {
    let db = DB::default();
    let db = &*db;
    let toolchain = db.dev_toolchain().unwrap();
    let item_path_menu = item_path_menu(db, toolchain);
    let array_ty_decl = item_path_menu.array_ty_path().syn_decl(db).unwrap();
    assert_eq!(array_ty_decl.template_parameters(db).len(), 2);
}
