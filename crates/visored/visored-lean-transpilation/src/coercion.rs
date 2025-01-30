use crate::*;
use lean_coword::ident::LnIdent;
use lean_entity_path::{
    theorem::{LnTermDerivationTheoremPath, LnTheoremPath},
    LnItemPath,
};
use lean_mir_expr::expr::{LnMirExprData, LnMirExprEntry};
use visored_mir_expr::coercion::{VdMirCoercion, VdMirSeparatorCoercion};
use visored_term::{menu::VdTypeMenu, ty::VdType};

impl<S> VdTranspileToLean<S, LnMirExprEntry> for VdMirCoercion
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        match self {
            VdMirCoercion::BinaryOpr(slf) => todo!(),
            VdMirCoercion::Separator(slf) => {
                let ident = create_separator_coercion_ident(slf, builder);
                LnMirExprEntry::new(LnMirExprData::ItemPath(LnItemPath::Theorem(
                    LnTheoremPath::TermDerivation(LnTermDerivationTheoremPath::Custom(ident)),
                )))
            }
        }
    }
}

fn create_separator_coercion_ident<S>(
    signature: VdMirSeparatorCoercion,
    builder: &VdLeanTranspilationBuilder<S>,
) -> LnIdent
where
    S: IsVdLeanTranspilationScheme,
{
    let separator = signature.opr().code();
    let source_ty = signature.source_ty();
    let target_ty = signature.target_ty();
    if source_ty == target_ty {
        return LnIdent::from_owned(format!("{separator}_identity_coercion"), builder.db());
    }
    let ty_menu = builder.ty_menu();
    let source_ty = ty_code(source_ty, ty_menu);
    let target_ty = ty_code(target_ty, ty_menu);
    LnIdent::from_owned(
        format!("{separator}_{source_ty}_to_{target_ty}_coercion"),
        builder.db(),
    )
}

fn ty_code(ty: VdType, ty_menu: &VdTypeMenu) -> &'static str {
    if ty == ty_menu.nat {
        "nat"
    } else if ty == ty_menu.int {
        "int"
    } else if ty == ty_menu.rat {
        "rat"
    } else if ty == ty_menu.real {
        "real"
    } else if ty == ty_menu.complex {
        "complex"
    } else {
        todo!()
    }
}
