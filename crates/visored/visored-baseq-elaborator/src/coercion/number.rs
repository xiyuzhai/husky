use super::*;

impl<'sess> VdBsqExpr<'sess> {
    pub fn is_real(
        &self,
        elaborator: &mut VdBsqElaboratorInner<'_, 'sess>,
    ) -> VdBsqCoercionOutcome<'sess> {
        match *self.ty() {
            VdTerm::ItemPath(path) => match path.item_path() {
                VdItemPath::Category(vd_category_path) => todo!(),
                VdItemPath::Set(path) => match path {
                    VdSetPath::Prelude(path) => match path {
                        VdPreludeSetPath::NaturalNumber
                        | VdPreludeSetPath::RationalNumber
                        | VdPreludeSetPath::Integer => {
                            VdBsqCoercionOutcome::TriviallyTrue(VdBsqTrivialCoercion::NumberToReal)
                        }
                        VdPreludeSetPath::RealNumber => {
                            VdBsqCoercionOutcome::TriviallyTrue(VdBsqTrivialCoercion::Identity)
                        }
                        VdPreludeSetPath::ComplexNumber => todo!(),
                        _ => todo!(),
                    },
                },
                VdItemPath::Function(vd_function_path) => todo!(),
                VdItemPath::Trait(vd_trait_path) => todo!(),
                VdItemPath::TraitItem(vd_trait_item_path) => todo!(),
                VdItemPath::Prop(vd_prop_path) => todo!(),
            },
            _ => todo!(),
        }
    }
}
