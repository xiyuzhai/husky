use crate::*;
use dictionary::item_path::VdItemPathTranslation;
use lean_mir_expr::expr::{LnMirExprData, LnMirExprEntry, LnMirExprIdx};
use lean_term::ty::LnType;
use visored_entity_path::path::VdItemPath;
use visored_term::{
    term::VdTermData,
    ty::{VdType, VdTypeData},
};

pub enum VdTypeLeanTranspilation {
    Type(LnMirExprIdx),
}

impl<'a, Scheme> VdTranspileToLean<Scheme, VdTypeLeanTranspilation> for VdType
where
    Scheme: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<Scheme>) -> VdTypeLeanTranspilation {
        let db = builder.db();
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

impl<'a, Scheme> VdLeanTranspilationBuilder<'a, Scheme>
where
    Scheme: IsVdLeanTranspilationScheme,
{
    fn build_ln_ty_from_vd_item_path(&mut self, item_path: VdItemPath) -> LnMirExprIdx {
        let Some(translation) = self.dictionary().item_path_translation(item_path) else {
            todo!("item path not found in dictionary, item path: {item_path:?}")
        };
        let data = match *translation {
            VdItemPathTranslation::ItemPath(ln_item_path) => LnMirExprData::ItemPath(ln_item_path),
        };
        let entry = LnMirExprEntry::new(data);
        self.alloc_expr(entry)
    }
}
