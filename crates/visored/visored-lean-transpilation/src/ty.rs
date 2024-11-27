use crate::*;
use dictionary::item_path::VdItemPathTranslation;
use lean_mir_expr::expr::{LnMirExprData, LnMirExprIdx};
use lean_term::ty::LnType;
use visored_entity_path::path::VdItemPath;
use visored_term::{
    term::VdTermData,
    ty::{VdType, VdTypeData},
};

pub enum VdTypeLeanTranspilation {
    Type(LnMirExprIdx),
}

impl VdTranspileToLean<VdTypeLeanTranspilation> for VdType {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> VdTypeLeanTranspilation {
        match *self.data() {
            VdTermData::Literal(_) => todo!(),
            VdTermData::ItemPath(ref item_path) => VdTypeLeanTranspilation::Type(
                builder.build_ln_ty_from_vd_item_path(item_path.item_path()),
            ),
            VdTermData::ForAll(_) => todo!(),
            VdTermData::Exists(_) => todo!(),
            VdTermData::Limit(_) => todo!(),
            VdTermData::Eval(_) => todo!(),
            VdTermData::SymbolicVariable(_) => todo!(),
            VdTermData::AbstractVariable(_) => todo!(),
            VdTermData::StackVariable(_) => todo!(),
            VdTermData::Application(_) => todo!(),
            VdTermData::Abstraction(_) => todo!(),
        }
    }
}

impl<'a> VdLeanTranspilationBuilder<'a> {
    fn build_ln_ty_from_vd_item_path(&mut self, item_path: VdItemPath) -> LnMirExprIdx {
        let Some(translation) = self.dictionary().item_path_translation(item_path) else {
            todo!()
        };
        let data = match *translation {
            VdItemPathTranslation::ItemPath(ln_item_path) => LnMirExprData::ItemPath(ln_item_path),
        };
        self.alloc_expr(data)
    }
}
