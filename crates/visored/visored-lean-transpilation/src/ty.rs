use crate::*;
use dictionary::item_path::VdItemPathTranslation;
use lean_mir_expr::expr::{LnMirExprData, LnMirExprIdx};
use lean_term::ty::LnType;
use visored_term::ty::{VdType, VdTypeData};

pub enum VdTypeLeanTranspilation {
    Type(LnMirExprIdx),
}

impl VdTranspileToLean<VdTypeLeanTranspilation> for VdType {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> VdTypeLeanTranspilation {
        let db = builder.db();
        if self.refinements(db).is_empty() {
            VdTypeLeanTranspilation::Type(builder.build_ln_ty_from_vd_ty_without_refinements(self))
        } else {
            todo!()
        }
    }
}

impl<'a> VdLeanTranspilationBuilder<'a> {
    fn build_ln_ty_from_vd_ty_without_refinements(&mut self, ty: VdType) -> LnMirExprIdx {
        debug_assert!(ty.refinements(self.db()).is_empty());
        let data = match ty.data(self.db()) {
            VdTypeData::ItemPath(path) => {
                let Some(translation) = self.dictionary().item_path_translation(path) else {
                    todo!()
                };
                match *translation {
                    VdItemPathTranslation::ItemPath(ln_item_path) => {
                        LnMirExprData::ItemPath(ln_item_path)
                    }
                }
            }
        };
        self.alloc_expr(data)
    }
}
