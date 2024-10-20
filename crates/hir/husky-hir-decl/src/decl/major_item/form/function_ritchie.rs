use super::*;
use husky_entity_kind::ritchie::RitchieItemKind;
use husky_syn_decl::decl::major_item::form::function_ritchie::MajorFunctionRitchieSynDecl;

#[salsa::interned]
pub struct MajorFunctionRitchieHirDecl {
    pub path: MajorFormPath,
    pub ritchie_item_kind: RitchieItemKind,
    #[return_ref]
    pub template_parameters: HirTemplateParameters,
    #[return_ref]
    pub parenate_parameters: HirParenateParameters,
    pub return_ty: HirType,
    pub hir_expr_region: HirExprRegion,
}

impl MajorFunctionRitchieHirDecl {
    pub(super) fn from_syn(
        path: MajorFormPath,
        syn_decl: MajorFunctionRitchieSynDecl,
        db: &::salsa::Db,
    ) -> Self {
        let builder = HirDeclBuilder::new(syn_decl.syn_expr_region(db), db);
        let ritchie_item_kind = syn_decl.ritchie_item_kind(db);
        let template_parameters =
            HirTemplateParameters::from_syn(syn_decl.template_parameters(db), &builder);
        let parenate_parameters: HirParenateParameters = match ritchie_item_kind {
            RitchieItemKind::Fn => {
                HirEagerParenateParameters::from_syn(syn_decl.parenate_parameters(db), &builder)
                    .into()
            }
            RitchieItemKind::Gn => {
                HirLazyParenateParameters::from_syn(syn_decl.parenate_parameters(db), &builder)
                    .into()
            }
            RitchieItemKind::Vn => todo!(),
            RitchieItemKind::Pn => todo!(),
            RitchieItemKind::Qn => todo!(),
            RitchieItemKind::Bn => todo!(),
            RitchieItemKind::Sn => todo!(),
            RitchieItemKind::Tn => todo!(),
        };
        let return_ty = builder.return_ty_before_colon(syn_decl.return_ty(db));
        Self::new(
            db,
            path,
            ritchie_item_kind,
            template_parameters,
            parenate_parameters,
            return_ty,
            builder.finish(),
        )
    }
}
