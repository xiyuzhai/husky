use crate::*;
use lean_coword::ident::LnIdent;
use lean_entity_path::{
    theorem::{LnTermDerivationTheoremPath, LnTheoremPath},
    LnItemPath,
};
use lean_mir_expr::expr::{LnMirExprData, LnMirExprEntry};
use visored_mir_expr::coercion::{
    pow::VdMirPowCoercion, triangle::VdMirCoercionTriangle, VdMirBinaryOprCoercion, VdMirCoercion,
    VdMirPrefixOprCoercion, VdMirSeparatorCoercion,
};
use visored_term::{menu::VdTypeMenu, ty::VdType};

impl<S> VdTranspileToLean<S, LnMirExprEntry> for VdMirCoercion
where
    S: IsVdLeanTranspilationScheme,
{
    #[track_caller]
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        let ident = match self {
            VdMirCoercion::Triangle(slf) => create_triangle_coercion_ident(slf, builder),
            VdMirCoercion::PrefixOpr(slf) => create_prefix_opr_coercion_ident(slf, builder),
            VdMirCoercion::BinaryOpr(slf) => create_binary_opr_coercion_ident(slf, builder),
            VdMirCoercion::Separator(slf) => create_separator_coercion_ident(slf, builder),
            VdMirCoercion::Pow(slf) => create_pow_coercion_ident(slf, builder),
        };
        LnMirExprEntry::new(LnMirExprData::ItemPath(LnItemPath::Theorem(
            LnTheoremPath::TermDerivation(LnTermDerivationTheoremPath::Custom(ident)),
        )))
    }
}

fn create_triangle_coercion_ident<S>(
    signature: VdMirCoercionTriangle,
    builder: &VdLeanTranspilationBuilder<S>,
) -> LnIdent
where
    S: IsVdLeanTranspilationScheme,
{
    let src = ty_code(signature.src, builder.ty_menu());
    let mid = ty_code(signature.mid, builder.ty_menu());
    let dst = ty_code(signature.dst, builder.ty_menu());
    LnIdent::from_owned(format!("{src}_{mid}_{dst}_coercion_triangle"), builder.db())
}

fn create_prefix_opr_coercion_ident<S>(
    signature: VdMirPrefixOprCoercion,
    builder: &VdLeanTranspilationBuilder<S>,
) -> LnIdent
where
    S: IsVdLeanTranspilationScheme,
{
    let prefix = signature.opr().code();
    let source_ty = signature.source_ty();
    let target_ty = signature.target_ty();
    if source_ty == target_ty {
        return LnIdent::from_owned(format!("{prefix}_identity_coercion"), builder.db());
    }
    let ty_menu = builder.ty_menu();
    let source_ty = ty_code(source_ty, ty_menu);
    let target_ty = ty_code(target_ty, ty_menu);
    LnIdent::from_owned(
        format!("{prefix}_{source_ty}_to_{target_ty}_coercion"),
        builder.db(),
    )
}

fn create_binary_opr_coercion_ident<S>(
    signature: VdMirBinaryOprCoercion,
    builder: &VdLeanTranspilationBuilder<S>,
) -> LnIdent
where
    S: IsVdLeanTranspilationScheme,
{
    let binary_opr = signature.opr().code();
    let source_ty = signature.source_ty();
    let target_ty = signature.target_ty();
    if source_ty == target_ty {
        return LnIdent::from_owned(format!("{binary_opr}_identity_coercion"), builder.db());
    }
    let ty_menu = builder.ty_menu();
    let source_ty = ty_code(source_ty, ty_menu);
    let target_ty = ty_code(target_ty, ty_menu);
    LnIdent::from_owned(
        format!("{binary_opr}_{source_ty}_to_{target_ty}_coercion"),
        builder.db(),
    )
}

#[track_caller]
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

fn create_pow_coercion_ident<S>(
    coercion: VdMirPowCoercion,
    builder: &VdLeanTranspilationBuilder<S>,
) -> LnIdent
where
    S: IsVdLeanTranspilationScheme,
{
    let ty_menu = builder.ty_menu();
    let src_base_ty = ty_code(coercion.src_base_ty, ty_menu);
    let src_exponent_ty = ty_code(coercion.src_exponent_ty, ty_menu);
    let dst_base_ty = ty_code(coercion.dst_base_ty, ty_menu);
    let dst_exponent_ty = ty_code(coercion.dst_exponent_ty, ty_menu);
    LnIdent::from_owned(
        format!(
            "{src_base_ty}_pow_{src_exponent_ty}_to_{dst_base_ty}_pow_{dst_exponent_ty}_coercion"
        ),
        builder.db(),
    )
}

#[track_caller]
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
        todo!("ty = {:?}", ty)
    }
}
