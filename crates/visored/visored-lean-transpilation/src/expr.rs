pub mod application;
mod separated_list;

use super::VdTranspileToLean;
use crate::{
    builder::VdLeanTranspilationBuilder,
    dictionary::{func_key::VdFuncKeyTranslation, item_path::VdItemPathTranslation},
    scheme::IsVdLeanTranspilationScheme,
    ty::VdTypeLeanTranspilation,
};
use either::*;
use lean_entity_path::LnItemPath;
use lean_mir_expr::expr::{
    application::LnMirFunc, LnMirExprData, LnMirExprEntry, LnMirExprIdx, LnMirExprIdxRange,
};
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::term::literal::{LnLiteral, LnLiteralData};
use visored_entity_path::path::{trai_item::VdTraitItemPath, VdItemPath};
use visored_mir_expr::{
    derivation::{construction::term::VdMirTermDerivationIdx, VdMirDerivationIdx},
    expr::{
        application::{VdMirFunc, VdMirFuncKey},
        VdMirExprData, VdMirExprIdx, VdMirExprIdxRange,
    },
};
use visored_mir_opr::separator::chaining::VdMirBaseChainingSeparator;
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;
use visored_term::term::literal::{VdLiteral, VdLiteralData, VdSign};

impl<'db, S> VdTranspileToLean<S, LnMirExprIdx> for VdMirExprIdx
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprIdx {
        let entry = builder.build_expr_entry(self);
        builder.alloc_expr(entry)
    }
}

impl<'db, S, I> VdTranspileToLean<S, LnMirExprIdxRange> for I
where
    S: IsVdLeanTranspilationScheme,
    I: Copy + IntoIterator,
    I::Item: VdTranspileToLean<S, LnMirExprEntry>,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprIdxRange {
        let mut exprs = vec![];
        for expr in self {
            let entry = expr.to_lean(builder);
            exprs.push(entry);
        }
        builder.alloc_exprs(exprs)
    }
}

impl<'db, S> VdTranspileToLean<S, LnMirExprEntry> for VdMirExprIdx
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        builder.build_expr_entry(self)
    }
}

impl<'db, S> VdTranspileToLean<S, LnMirExprEntry> for VdMirDerivationIdx
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        let ident = builder.mangle_derivation(self);
        LnMirExprEntry::new(LnMirExprData::Variable { ident })
    }
}

impl<'db, S> VdTranspileToLean<S, LnMirExprEntry> for &VdMirDerivationIdx
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        VdMirDerivationIdx::to_lean(*self, builder)
    }
}

impl<'db, S> VdTranspileToLean<S, LnMirExprEntry> for VdMirTermDerivationIdx
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        VdMirDerivationIdx::to_lean(*self, builder)
    }
}

impl<'db, S> VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(crate) fn build_expr_entry(&mut self, expr: VdMirExprIdx) -> LnMirExprEntry {
        let data = self.build_expr_data(expr);
        let entry = &self.expr_arena()[expr];
        let ty = entry.ty();
        let ty_ascription = if let Some(expected_ty) = entry.expected_ty() {
            if ty != expected_ty {
                match expected_ty.to_lean(self) {
                    VdTypeLeanTranspilation::Type(expected_ty) => Some(expected_ty),
                }
            } else {
                None
            }
        } else {
            None
        };
        match ty_ascription {
            Some(ty_ascription) => LnMirExprEntry::new(LnMirExprData::TypeAscription {
                expr: self.alloc_expr(LnMirExprEntry::new(data)),
                ty_ascription,
            }),
            None => LnMirExprEntry::new(data),
        }
    }

    fn build_expr_data(&mut self, expr: VdMirExprIdx) -> LnMirExprData {
        let db = self.db();
        match *self.expr_arena()[expr].data() {
            VdMirExprData::Literal(literal) => LnMirExprData::Literal(to_lean_literal(literal, db)),
            VdMirExprData::ItemPath(item_path) => {
                let Some(translation) = self.dictionary().item_path_translation(item_path) else {
                    todo!("item path not found, `{:?}`", item_path)
                };
                match *translation {
                    VdItemPathTranslation::ItemPath(item_path) => {
                        LnMirExprData::ItemPath(item_path)
                    }
                }
            }
            // TODO: consider variable deps
            VdMirExprData::Variable(local_defn) => LnMirExprData::Variable {
                ident: self.mangle_symbol(local_defn),
            },
            VdMirExprData::Application {
                function,
                arguments,
            } => self.build_application(expr, function, arguments),
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => self.build_folding_separated_list(leader, followers),
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => self.build_chaining_separated_list(leader, followers, joined_signature),
        }
    }
}

#[eterned::memo]
fn to_lean_literal(literal: VdLiteral, db: &EternerDb) -> LnLiteral {
    let data = match *literal.data() {
        VdLiteralData::Int(ref i) => match i.sign() {
            VdSign::Minus => LnLiteralData::Int(format!("({i}:ℤ)")),
            VdSign::Plus | VdSign::NoSign => LnLiteralData::Nat(format!("({i}:ℕ)")),
        },
        VdLiteralData::Frac(ref lit) => {
            LnLiteralData::Frac(format!("({} : ℚ) / {}", lit.numerator(), lit.denominator()))
        }
    };
    LnLiteral::new(data, db)
}

impl<'db, S> VdTranspileToLean<S, LnMirFunc> for VdMirFunc
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirFunc {
        match self.key_or_expr() {
            Left(key) => {
                let Some(translation) = builder.dictionary().func_key_translation(key) else {
                    todo!()
                };
                match *translation {
                    VdFuncKeyTranslation::PrefixOpr(func_key)
                    | VdFuncKeyTranslation::FoldingBinaryOpr(func_key)
                    | VdFuncKeyTranslation::ChainingBinaryOpr(func_key)
                    | VdFuncKeyTranslation::Power(func_key)
                    | VdFuncKeyTranslation::Function(func_key)
                    | VdFuncKeyTranslation::JustBinaryOpr(func_key) => {
                        builder.build_func_from_key(func_key)
                    }
                    VdFuncKeyTranslation::InSet => LnMirFunc::InSet,
                }
            }
            Right(_) => todo!(),
        }
    }
}

impl<'db, S> VdTranspileToLean<S, LnMirFunc> for VdBaseChainingSeparatorSignature
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirFunc {
        builder.build_func_from_vd_key(self.into())
    }
}

impl<'db, S> VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    fn build_func_from_vd_key(&mut self, key: VdMirFuncKey) -> LnMirFunc {
        let Some(translation) = self.dictionary().func_key_translation(key) else {
            return self.build_func_from_vd_key_by_rule(key);
        };
        match *translation {
            VdFuncKeyTranslation::PrefixOpr(func_key)
            | VdFuncKeyTranslation::FoldingBinaryOpr(func_key)
            | VdFuncKeyTranslation::ChainingBinaryOpr(func_key)
            | VdFuncKeyTranslation::Power(func_key)
            | VdFuncKeyTranslation::Function(func_key)
            | VdFuncKeyTranslation::JustBinaryOpr(func_key) => self.build_func_from_key(func_key),
            VdFuncKeyTranslation::InSet => LnMirFunc::InSet,
        }
    }

    fn build_func_from_vd_key_by_rule(&mut self, key: VdMirFuncKey) -> LnMirFunc {
        match key {
            VdMirFuncKey::NormalBasePrefixOpr(vd_instantiation) => todo!(),
            VdMirFuncKey::NormalBaseSeparator(instantiation) => match instantiation.path() {
                VdItemPath::Prop(vd_prop_path) => todo!(),
                VdItemPath::Category(vd_category_path) => todo!(),
                VdItemPath::Set(vd_set_path) => todo!(),
                VdItemPath::Function(vd_function_path) => todo!(),
                VdItemPath::Trait(vd_trait_path) => todo!(),
                VdItemPath::TraitItem(trait_item_path) => match trait_item_path {
                    VdTraitItemPath::Iff => LnMirFunc::Iff,
                    VdTraitItemPath::InSet => LnMirFunc::InSet,
                    VdTraitItemPath::GroupMul => todo!(),
                    VdTraitItemPath::AbelianGroupAdd => {
                        todo!()
                    }
                    VdTraitItemPath::NatAdd => todo!(),
                    VdTraitItemPath::NatMul => todo!(),
                    VdTraitItemPath::CommRingAdd => todo!(),
                    VdTraitItemPath::CommRingSub => todo!(),
                    VdTraitItemPath::CommRingMul => todo!(),
                    VdTraitItemPath::CommRingPower => todo!(),
                    VdTraitItemPath::CommRingPos => todo!(),
                    VdTraitItemPath::CommRingNeg => todo!(),
                    VdTraitItemPath::Eq => todo!(),
                    VdTraitItemPath::Ne => todo!(),
                    VdTraitItemPath::Lt => todo!(),
                    VdTraitItemPath::Gt => todo!(),
                    VdTraitItemPath::Le => todo!(),
                    VdTraitItemPath::Ge => todo!(),
                    VdTraitItemPath::FieldDiv => todo!(),
                    VdTraitItemPath::RealSqrt => todo!(),
                },
            },
            VdMirFuncKey::NormalBaseBinaryOpr(vd_instantiation) => todo!(),
            VdMirFuncKey::Power(vd_instantiation) => todo!(),
            VdMirFuncKey::NormalBaseSqrt(vd_instantiation) => todo!(),
        }
    }
}
