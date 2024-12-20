use either::Either;
use husky_entity_path::path::major_item::trai::PreludeTraitPath;
use husky_hir_decl::decl::HasHirDecl;
use husky_hir_defn::defn::assoc_item::trai_for_ty_item::{
    assoc_ritchie::TraitForTypeAssocRitchieHirDefn, assoc_ty::TraitForTypeAssocTypeHirDefn,
    assoc_val::TraitForTypeAssocValHirDefn, method_ritchie::TraitForTypeMethodRitchieHirDefn,
    TraitForTypeItemHirDefn,
};
use husky_hir_ty::{HirComptermTemplateVariable, HirTemplateVariable, HirTemplateVariableClass};
use smallvec::SmallVec;

use super::*;
use crate::builder::keyword::RustKeyword;

impl TranspileToRustWith for TraitForTypeItemHirDefn {
    fn transpile_to_rust(self, builder: &mut RustTranspilationBuilder) {
        match self {
            TraitForTypeItemHirDefn::AssocRitchie(hir_defn) => hir_defn.transpile_to_rust(builder),
            TraitForTypeItemHirDefn::MethodFn(hir_defn) => hir_defn.transpile_to_rust(builder),
            TraitForTypeItemHirDefn::AssocType(hir_defn) => hir_defn.transpile_to_rust(builder),
            TraitForTypeItemHirDefn::AssocVal(hir_defn) => hir_defn.transpile_to_rust(builder),
        }
    }
}

impl TranspileToRustWith for TraitForTypeAssocRitchieHirDefn {
    fn transpile_to_rust(self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let Some((body, hir_eager_expr_region)) = self.eager_body_with_hir_eager_expr_region(db)
        else {
            return;
        };
        builder.keyword(RustKeyword::Fn);
        let path = self.path(db);
        path.ident(db).transpile_to_rust(builder);
        let hir_decl = self.hir_decl(db);
        builder.with_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db), |builder| {
            hir_decl.template_parameters(db).transpile_to_rust(builder);
            let impl_block_path = path.impl_block(db);
            match impl_block_path.trai_path(db).refine(db) {
                Either::Left(PreludeTraitPath::UNVEIL) => builder
                    .delimited_heterogeneous_list_with(RustDelimiter::Par, |builder| {
                        builder.heterogeneous_comma_list_items(
                            hir_decl.parenate_parameters(db).iter(),
                        );
                        builder.heterogeneous_comma_list_item_with(|builder| {
                            let hir_decl = impl_block_path.hir_decl(db).unwrap();
                            let runtime_const_symbols: SmallVec<[HirComptermTemplateVariable; 4]> =
                                hir_decl
                                    .template_parameters(db)
                                    .iter()
                                    .filter_map(|param| match param.symbol() {
                                        HirTemplateVariable::Compterm(symbol) => {
                                            (symbol.index(db).class()
                                                == HirTemplateVariableClass::Poly)
                                                .then_some(symbol)
                                        }
                                        _ => None,
                                    })
                                    .collect();
                            builder.with_hir_eager_expr_region(
                                hir_decl.hir_eager_expr_region(db),
                                |builder| {
                                    builder.delimited_comma_list_with_last_comma(
                                        RustDelimiter::Par,
                                        runtime_const_symbols.iter().copied(),
                                    );
                                    builder.punctuation(RustPunctuation::Colon);
                                    builder.punctuation(RustPunctuation::Ambersand);
                                    builder.delimited_comma_list_with_last_comma(
                                        RustDelimiter::Par,
                                        runtime_const_symbols.iter().map(|symbol| symbol.ty(db)),
                                    );
                                    use husky_print_utils::p;
                                    p!(builder.result());
                                    todo!();
                                },
                            )
                        })
                    }),
                _ => hir_decl.parenate_parameters(db).transpile_to_rust(builder),
            }
            builder.return_ty(hir_decl.return_ty(db))
        });
        builder.eager_body(hir_eager_expr_region, body)
    }
}

impl TranspileToRustWith for TraitForTypeMethodRitchieHirDefn {
    fn transpile_to_rust(self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let Some((body, hir_eager_expr_region)) = self.eager_body_with_hir_eager_expr_region(db)
        else {
            return;
        };
        builder.keyword(RustKeyword::Fn);
        let path_ident = self.path(db).ident(db);
        path_ident.transpile_to_rust(builder);
        let hir_decl = self.hir_decl(db);
        builder.with_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db), |builder| {
            hir_decl.template_parameters(db).transpile_to_rust(builder);
            builder.delimited_heterogeneous_list_with(RustDelimiter::Par, |builder| {
                builder.heterogeneous_comma_list_item(hir_decl.self_value_parameter(db));
                builder.heterogeneous_comma_list_items(hir_decl.parenate_parameters(db).iter());
                if path_ident.data() == "visualize" {
                    builder.visual_synchrotron_parameter_decl()
                }
            });
            builder.return_ty(hir_decl.return_ty(db))
        });
        builder.eager_body(hir_eager_expr_region, body)
    }
}

impl TranspileToRustWith for TraitForTypeAssocTypeHirDefn {
    fn transpile_to_rust(self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let hir_decl = self.hir_decl(db);
        builder.with_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db), |builder| {
            builder.on_fresh_semicolon_line(|builder| {
                builder.keyword(RustKeyword::Type);
                self.path(db).ident(db).transpile_to_rust(builder);
                builder.punctuation(RustPunctuation::Assign);
                hir_decl.ty(db).transpile_to_rust(builder)
            })
        })
    }
}

impl TranspileToRustWith for TraitForTypeAssocValHirDefn {
    fn transpile_to_rust(self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let hir_decl = self.hir_decl(db);
        builder.val_attr(
            hir_decl.path(db).into(),
            todo!(),
            hir_decl.return_ty(db).always_copyable(db),
        );
        todo!()
    }
}
