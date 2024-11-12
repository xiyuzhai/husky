use self::coercion::VmirCoercion;
use crate::{
    destroyer::VmirDestroyerIdxRange, eval::EvalVmir, pattern::VmirPattern, stmt::VmirStmtIdxRange,
    *,
};
use either::*;
use husky_coword::Ident;
use husky_entity_kind::MajorFormKind;
use husky_entity_path::path::{
    major_item::{form::MajorFormPath, MajorItemPath},
    PrincipalEntityPath,
};
use husky_hir_decl::decl::{HasHirDecl, TypeVariantHirDecl};
use husky_hir_eager_expr::{
    variable::runtime::{HirEagerRuntimeVariableIdx, HirEagerRuntimeVariableName},
    HirEagerExprData, HirEagerExprIdx, HirEagerRitchieArgument,
};
use husky_hir_opr::{binary::HirBinaryOpr, prefix::HirPrefixOpr, suffix::HirSuffixOpr};
use husky_ki::KiRuntimeCompterm;
use husky_ki_repr::expansion::ki_runtime_compterms_from_hir_instantiation;
use husky_lifetime_utils::capture::Captures;
use husky_linket::{linket::Linket, template_argument::qual::LinQual};
use husky_linket_impl::{linket_impl::VmArgumentValue, LinketImplVmControlFlowThawed};
use husky_literal_value::LiteralValue;
use husky_opr::{BinaryClosedOpr, BinaryComparisonOpr, BinaryShiftOpr};
use husky_place::place::{idx::PlaceIdx, EthPlace};
use husky_value::{vm_control_flow::VmControlFlow, IsThawedValue};
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange};
use salsa::DebugWithDb;
use smallvec::{smallvec, SmallVec};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum VmirExprData<LinketImpl: IsLinketImpl> {
    Literal {
        value: LiteralValue,
    },
    RuntimeVariable {
        name: HirEagerRuntimeVariableName,
        variable_idx: HirEagerRuntimeVariableIdx,
        qual: LinQual,
    },
    Binary {
        lopd: VmirExprIdx<LinketImpl>,
        opr: HirBinaryOpr,
        ropd: VmirExprIdx<LinketImpl>,
    },
    Be {
        opd: VmirExprIdx<LinketImpl>,
        pattern: VmirPattern<LinketImpl>,
    },
    Prefix {
        opr: HirPrefixOpr,
        opd: VmirExprIdx<LinketImpl>,
    },
    Suffix {
        opd: VmirExprIdx<LinketImpl>,
        opr: HirSuffixOpr,
    },
    Unveil {
        linket_impl: LinketImpl,
        opd: VmirExprIdx<LinketImpl>,
        runtime_compterms: SmallVec<[KiRuntimeCompterm; 4]>,
    },
    Linket {
        linket_impl: LinketImpl,
        arguments: VmirArguments<LinketImpl>,
    },
    Block {
        stmts: VmirStmtIdxRange<LinketImpl>,
        destroyers: VmirDestroyerIdxRange,
    },
    Closure,
    Todo,
    Unreachable,
    As {
        opd: VmirExprIdx<LinketImpl>,
    },
    Index {
        self_argument: VmirExprIdx<LinketImpl>,
        items: VmirExprIdxRange<LinketImpl>,
    },
    Val {
        linket_impl_or_val_path: Either<LinketImpl, MajorFormPath>,
    },
    UnitTypeVariant {
        linket_impl: LinketImpl,
    },
    Unwrap {
        opd: VmirExprIdx<LinketImpl>,
    },
    ConstTemplateVariable,
    RitchieItemPath,
    StaticVar {
        linket_impl: LinketImpl,
    },
}

pub type VmirExprArena<LinketImpl> = Arena<VmirExprData<LinketImpl>>;
pub type VmirExprMap<LinketImpl, T> = ArenaMap<VmirExprData<LinketImpl>, T>;

// TODO clean up
#[salsa::derive_debug_with_db]
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct VmirExprIdx<LinketImpl: IsLinketImpl>(pub(crate) ArenaIdx<VmirExprData<LinketImpl>>);

impl<LinketImpl: IsLinketImpl> std::fmt::Debug for VmirExprIdx<LinketImpl> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("VmirExprIdx").field(&self.0).finish()
    }
}

impl<LinketImpl: IsLinketImpl> std::ops::Deref for VmirExprIdx<LinketImpl> {
    type Target = ArenaIdx<VmirExprData<LinketImpl>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VmirExprIdxRange<LinketImpl: IsLinketImpl>(
    pub(crate) ArenaIdxRange<VmirExprData<LinketImpl>>,
);

impl<LinketImpl: IsLinketImpl> IntoIterator for VmirExprIdxRange<LinketImpl> {
    type Item = VmirExprIdx<LinketImpl>;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(VmirExprIdx)
    }
}

impl<LinketImpl: IsLinketImpl> IntoIterator for &VmirExprIdxRange<LinketImpl> {
    type Item = VmirExprIdx<LinketImpl>;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(VmirExprIdx)
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum VmirArgument<LinketImpl: IsLinketImpl> {
    SelfValue {
        expr: VmirExprIdx<LinketImpl>,
    },
    Simple {
        expr: VmirExprIdx<LinketImpl>,
        coercion: VmirCoercion,
    },
    Variadic {
        exprs: VmirExprIdxRange<LinketImpl>,
    },
}
pub type VmirArguments<LinketImpl> = SmallVec<[VmirArgument<LinketImpl>; 4]>;

impl<LinketImpl: IsLinketImpl> ToVmir<LinketImpl> for HirEagerExprIdx {
    type Output = VmirExprIdx<LinketImpl>;

    fn to_vmir<Linktime: IsLinktime<LinketImpl = LinketImpl>>(
        self,
        builder: &mut VmirBuilder<Linktime>,
    ) -> Self::Output {
        let expr_data = builder.build_vmir_expr(self);
        builder.alloc_expr(self, expr_data)
    }
}

impl<LinketImpl: IsLinketImpl> ToVmir<LinketImpl> for &SmallVec<[HirEagerExprIdx; 4]> {
    type Output = VmirExprIdxRange<LinketImpl>;

    fn to_vmir<Linktime: IsLinktime<LinketImpl = LinketImpl>>(
        self,
        builder: &mut VmirBuilder<Linktime>,
    ) -> Self::Output {
        let mut exprs = Vec::new();
        for &expr in self.iter() {
            exprs.push(builder.build_vmir_expr(expr));
        }
        builder.alloc_exprs(&self, exprs)
    }
}

impl<'comptime, Linktime: IsLinktime> VmirBuilder<'comptime, Linktime> {
    fn build_vmir_expr(&mut self, expr: HirEagerExprIdx) -> VmirExprData<Linktime::LinketImpl> {
        let db = self.db();
        let entry = &self.hir_eager_expr_arena()[expr];
        match *entry.data() {
            HirEagerExprData::Literal(lit) => VmirExprData::Literal {
                value: lit.into_literal_value(self.db()),
            },
            HirEagerExprData::PrincipalEntityPath {
                path,
                ref instantiation,
                ..
            } => match path {
                PrincipalEntityPath::Module(module_path) => {
                    todo!()
                }
                PrincipalEntityPath::MajorItem(major_item_path) => match major_item_path {
                    MajorItemPath::Type(ty_path) => todo!(),
                    MajorItemPath::Trait(trai_path) => todo!(),
                    MajorItemPath::Form(major_form_path) => match major_form_path.kind(db) {
                        MajorFormKind::Ritchie(ritchie_item_kind) => {
                            use husky_print_utils::p;
                            use salsa::DebugWithDb;
                            p!(path.debug(db));
                            VmirExprData::RitchieItemPath
                        }
                        MajorFormKind::TypeAlias => todo!(),
                        MajorFormKind::TypeVar => todo!(),
                        MajorFormKind::Val => {
                            let linket_or_val_path: Either<Linket, MajorFormPath> =
                                match Linket::new_val(major_form_path, db) {
                                    Some(linket) => Left(linket),
                                    None => Right(major_form_path),
                                };
                            let linket_impl_or_val_path = match linket_or_val_path {
                                Left(linket) => Left(self.linket_impl(linket)),
                                Right(ki_repr) => Right(ki_repr),
                            };
                            VmirExprData::Val {
                                linket_impl_or_val_path,
                            }
                        }
                        MajorFormKind::StaticMut => todo!(),
                        MajorFormKind::StaticVar => VmirExprData::StaticVar {
                            linket_impl: self.linket_impl(Linket::new_var(major_form_path, db)),
                        },
                        MajorFormKind::Compterm => todo!(),
                        MajorFormKind::Conceptual => todo!(),
                    },
                },
                PrincipalEntityPath::TypeVariant(type_variant_path) => {
                    let hir_decl = type_variant_path.hir_decl(db).unwrap();
                    match hir_decl {
                        TypeVariantHirDecl::Props(enum_props_variant_hir_decl) => todo!(),
                        TypeVariantHirDecl::Unit(enum_unit_type_variant_hir_decl) => {
                            VmirExprData::UnitTypeVariant {
                                linket_impl: self.linket_impl(
                                    Linket::new_ty_variant_constructor_fn(
                                        type_variant_path,
                                        instantiation,
                                        self.lin_instantiation(),
                                        db,
                                    ),
                                ),
                            }
                        }
                        TypeVariantHirDecl::Tuple(enum_tuple_variant_hir_decl) => todo!(),
                    }
                }
            },
            HirEagerExprData::AssocRitchie { assoc_item_path } => todo!(),
            HirEagerExprData::ComptimeVariable { ident } => VmirExprData::ConstTemplateVariable,
            HirEagerExprData::RuntimeVariable(variable_idx) => {
                let place_idx = match entry.quary().place() {
                    Some(place) => match place {
                        EthPlace::Idx(place_idx) => place_idx,
                        EthPlace::SymbolicVariable(_) => todo!(),
                        EthPlace::Field(_) => todo!(),
                    },
                    None => {
                        use husky_print_utils::p;

                        p!(entry.contracted_quary());
                        todo!()
                    }
                };
                let qual = LinQual::variable_qual(
                    entry.contracted_quary(),
                    entry.is_base_ty_always_copyable(),
                );
                VmirExprData::RuntimeVariable {
                    variable_idx,
                    qual,
                    name: variable_idx
                        .entry(self.hir_eager_runtime_variable_region_data().arena())
                        .name(),
                }
            }
            HirEagerExprData::Binary { lopd, opr, ropd } => VmirExprData::Binary {
                lopd: lopd.to_vmir(self),
                opr,
                ropd: ropd.to_vmir(self),
            },
            HirEagerExprData::Be { src, ref pattern } => VmirExprData::Be {
                opd: src.to_vmir(self),
                pattern: pattern.pattern.to_vmir(self),
            },
            HirEagerExprData::Prefix { opr, opd } => VmirExprData::Prefix {
                opr,
                opd: opd.to_vmir(self),
            },
            HirEagerExprData::Suffix { opd, opr } => VmirExprData::Suffix {
                opd: opd.to_vmir(self),
                opr,
            },
            HirEagerExprData::Unveil {
                unveil_assoc_fn_path,
                ref instantiation,
                opd,
                ..
            } => VmirExprData::Unveil {
                linket_impl: self.linket_impl(Linket::new_unveil_assoc_fn(
                    unveil_assoc_fn_path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                )),
                opd: opd.to_vmir(self),
                runtime_compterms: ki_runtime_compterms_from_hir_instantiation(instantiation, db),
            },
            HirEagerExprData::Unwrap { opd } => VmirExprData::Unwrap {
                opd: opd.to_vmir(self),
            },
            HirEagerExprData::As { opd, ty } => VmirExprData::As {
                opd: opd.to_vmir(self),
            },
            HirEagerExprData::TypeConstructorCall {
                path,
                ref instantiation,
                arguments: ref item_groups,
            } => {
                let linket = Linket::new_ty_constructor_fn(
                    path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = self.build_arguments(item_groups).collect();
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::TypeVariantConstructorCall {
                path,
                ref instantiation,
                ref arguments,
            } => {
                let linket = Linket::new_ty_variant_constructor_fn(
                    path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = self.build_arguments(arguments).collect();
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::FunctionRitchieCall {
                path,
                ref instantiation,
                ref arguments,
            } => {
                let linket = Linket::new_major_ritchie_item(
                    path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = self.build_arguments(arguments).collect();
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::AssocFunctionRitchieCall {
                path,
                ref instantiation,
                ref arguments,
            } => {
                let linket = Linket::new_assoc_function_ritchie_item(
                    path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = self.build_arguments(arguments).collect();
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::PropsStructField {
                self_argument,
                self_ty,
                ident,
                ..
            } => {
                let linket = Linket::new_props_struct_field(
                    self_ty,
                    ident,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = smallvec![VmirArgument::SelfValue {
                    expr: self_argument.to_vmir(self)
                }];
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::MemoizedField {
                self_argument,
                self_argument_ty,
                self_ty,
                ident,
                path,
                ref indirections,
                ref instantiation,
            } => {
                let linket = Linket::new_memo_field(
                    path,
                    instantiation,
                    self.lin_instantiation(),
                    self.db(),
                );
                let linket_impl = self.linket_impl(linket);
                let arguments = smallvec![VmirArgument::SelfValue {
                    expr: self_argument.to_vmir(self)
                }];
                if indirections.len() > 0 {
                    // ad hoc
                    // todo!()
                }
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::MethodRitchieCall {
                self_argument,
                self_ty,
                self_contract,
                ident,
                path,
                ref indirections,
                ref instantiation,
                arguments: ref hir_arguments,
            } => {
                let linket =
                    Linket::new_method(path, instantiation, self.lin_instantiation(), self.db());
                let linket_impl = self.linket_impl(linket);
                let mut arguments = smallvec![VmirArgument::SelfValue {
                    expr: self_argument.to_vmir(self)
                }];
                arguments.extend(self.build_arguments(hir_arguments));
                if indirections.len() > 0 {
                    // ad hoc
                    // todo!()
                }
                VmirExprData::Linket {
                    linket_impl,
                    arguments,
                }
            }
            HirEagerExprData::NewTuple { .. } => VmirExprData::Linket {
                linket_impl: todo!(),
                arguments: todo!(),
            },
            HirEagerExprData::Index {
                self_argument,
                ref items,
            } => VmirExprData::Index {
                self_argument: self_argument.to_vmir(self),
                items: items.to_vmir(self),
            },
            HirEagerExprData::NewList {
                exprs: ref hir_eager_exprs,
                element_ty,
            } => {
                let linket =
                    Linket::new_vec_constructor(element_ty, self.lin_instantiation(), self.db());
                let linket_impl = self.linket_impl(linket);
                VmirExprData::Linket {
                    linket_impl,
                    arguments: smallvec![VmirArgument::Variadic {
                        exprs: hir_eager_exprs.to_vmir(self),
                    }],
                }
            }
            HirEagerExprData::Block { stmts } => {
                VmirExprData::Block {
                    stmts: stmts.to_vmir(self),
                    // ad hoc, todo: find destroyers
                    destroyers: self.alloc_destroyers(vec![]),
                }
            }
            HirEagerExprData::Closure {
                ref parameters,
                return_ty,
                body,
            } => VmirExprData::Closure,
            HirEagerExprData::EmptyHtmlTag {
                function_ident,
                ref arguments,
            } => {
                let arguments = todo!();
                VmirExprData::Linket {
                    linket_impl: todo!(),
                    arguments,
                }
            }
            HirEagerExprData::Todo => VmirExprData::Todo,
            HirEagerExprData::Unreachable => VmirExprData::Unreachable,
        }
    }

    fn build_arguments<'a>(
        &'a mut self,
        arguments: &'comptime [HirEagerRitchieArgument],
    ) -> impl Iterator<Item = VmirArgument<Linktime::LinketImpl>> + Captures<'comptime> + 'a {
        arguments.iter().map(move |m| match m {
            HirEagerRitchieArgument::Simple(_, arg, coercion) => VmirArgument::Simple {
                expr: arg.to_vmir(self),
                coercion: coercion.to_vmir(self),
            },
            HirEagerRitchieArgument::Variadic => {
                todo!()
            }
            HirEagerRitchieArgument::Keyed => todo!(),
        })
    }
}

impl<LinketImpl: IsLinketImpl> VmirExprIdx<LinketImpl> {
    pub fn eval<'comptime>(
        self,
        coercion: impl Into<Option<VmirCoercion>>,
        ctx: &mut impl EvalVmir<'comptime, LinketImpl>,
    ) -> LinketImplVmControlFlowThawed<LinketImpl> {
        ctx.eval_expr(self, |ctx| self.eval_aux(coercion.into(), ctx))
    }

    // TODO: check that `.eval_expr_itself` is always used in all arms
    fn eval_aux<'comptime>(
        self,
        coercion: Option<VmirCoercion>,
        ctx: &mut impl EvalVmir<'comptime, LinketImpl>,
    ) -> LinketImplVmControlFlowThawed<LinketImpl> {
        use VmControlFlow::*;

        let db = ctx.db();

        let value = match *self.entry(ctx.vmir_expr_arena()) {
            VmirExprData::Literal { ref value } => {
                ctx.eval_expr_itself(self, |ctx| Continue(value.into_thawed_value()))
            }
            VmirExprData::RuntimeVariable {
                qual,
                name,
                variable_idx,
            } => ctx.eval_expr_itself(self, |ctx| {
                Continue(ctx.access_variable(variable_idx, qual))
            }),
            VmirExprData::Binary { lopd, opr, ropd } => {
                let mut lopd = lopd.eval(None, ctx)?;
                let ropd = ropd.eval(None, ctx)?;
                ctx.eval_expr_itself(self, |_ctx| match opr {
                    HirBinaryOpr::Closed(opr) => Continue(match opr {
                        BinaryClosedOpr::Add => lopd + ropd,
                        BinaryClosedOpr::BitAnd => lopd & ropd,
                        BinaryClosedOpr::BitOr => lopd | ropd,
                        BinaryClosedOpr::BitXor => lopd ^ ropd,
                        BinaryClosedOpr::Div => lopd / ropd,
                        BinaryClosedOpr::Mul => lopd * ropd,
                        BinaryClosedOpr::RemEuclid => todo!("be careful"),
                        BinaryClosedOpr::Power => todo!(),
                        BinaryClosedOpr::Sub => lopd - ropd,
                    }),
                    HirBinaryOpr::Shift(opr) => Continue(match opr {
                        BinaryShiftOpr::Shl => lopd << ropd,
                        BinaryShiftOpr::Shr => lopd >> ropd,
                    }),
                    HirBinaryOpr::Assign => {
                        lopd.assign(ropd);
                        Continue(().into())
                    }
                    HirBinaryOpr::AssignClosed(opr) => {
                        match opr {
                            BinaryClosedOpr::Add => lopd += ropd,
                            BinaryClosedOpr::BitAnd => todo!(),
                            BinaryClosedOpr::BitOr => todo!(),
                            BinaryClosedOpr::BitXor => todo!(),
                            BinaryClosedOpr::Div => todo!(),
                            BinaryClosedOpr::Mul => todo!(),
                            BinaryClosedOpr::RemEuclid => todo!(),
                            BinaryClosedOpr::Power => todo!(),
                            BinaryClosedOpr::Sub => todo!(),
                        }
                        Continue(().into())
                    }
                    HirBinaryOpr::AssignShift(_) => todo!(),
                    HirBinaryOpr::Comparison(opr) => Continue(
                        match opr {
                            BinaryComparisonOpr::Eq => lopd == ropd,
                            BinaryComparisonOpr::Neq => lopd != ropd,
                            BinaryComparisonOpr::Geq => lopd >= ropd,
                            BinaryComparisonOpr::Greater => lopd > ropd,
                            BinaryComparisonOpr::Leq => lopd <= ropd,
                            BinaryComparisonOpr::Less => lopd < ropd,
                        }
                        .into(),
                    ),
                    HirBinaryOpr::ShortCircuitLogic(_) => todo!(),
                })
            }
            VmirExprData::Be { opd, pattern } => todo!(),
            VmirExprData::Prefix { opr, opd } => {
                let opd = opd.eval(None, ctx)?;
                ctx.eval_expr_itself(self, |_ctx| match opr {
                    HirPrefixOpr::Minus => Continue(-opd),
                    HirPrefixOpr::NotBool => todo!(),
                    HirPrefixOpr::NotInt => todo!(),
                    HirPrefixOpr::BitNot => todo!(),
                    HirPrefixOpr::TakeRef => todo!(),
                    HirPrefixOpr::Deref => todo!(),
                })
            }
            VmirExprData::Suffix { opd, opr } => todo!(),
            VmirExprData::Unveil {
                linket_impl,
                opd,
                ref runtime_compterms,
            } => {
                let opd = opd.eval(None, ctx)?;
                ctx.eval_expr_itself(self, |ctx| {
                    linket_impl.eval_vm(
                        smallvec![
                            VmArgumentValue::Simple(opd),
                            VmArgumentValue::RuntimeConstants(unsafe {
                                std::mem::transmute(runtime_compterms as &[_])
                            }),
                        ],
                        db,
                    )
                })
            }
            VmirExprData::Linket {
                linket_impl,
                ref arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .map(
                        |arg| -> LinketImplVmControlFlowThawed<
                            LinketImpl,
                            VmArgumentValue<LinketImpl>,
                        > {
                            match arg {
                                VmirArgument::SelfValue { expr } => VmControlFlow::Continue(
                                    VmArgumentValue::Simple(expr.eval(None, ctx)?),
                                ),
                                VmirArgument::Simple { expr, coercion } => todo!(),
                                VmirArgument::Variadic { exprs } => {
                                    VmControlFlow::Continue(VmArgumentValue::Variadic(
                                        exprs
                                            .into_iter()
                                            .map(|expr| expr.eval(None, ctx))
                                            .collect::<VmControlFlow<_, _, _>>()?,
                                    ))
                                }
                            }
                        },
                    )
                    .collect::<VmControlFlow<_, _, _>>()?;
                ctx.eval_expr_itself(self, |ctx| linket_impl.eval_vm(arguments, ctx.db()))
            }
            VmirExprData::Block { stmts, destroyers } => stmts.eval(ctx),
            VmirExprData::Closure => todo!(),
            VmirExprData::Todo => todo!(),
            VmirExprData::Unreachable => todo!(),
            VmirExprData::As { opd } => todo!(),
            VmirExprData::Index {
                self_argument,
                items,
            } => {
                let self_argument = self_argument.eval(None, ctx)?;
                ctx.eval_expr_itself(self, |ctx| {
                    match items.0.len() {
                        1 => {
                            // TODO: ad hoc
                            let index = VmirExprIdx(items.0.start()).eval(None, ctx)?.to_usize();
                            self_argument.index(index).map_err(|_| todo!()).into()
                        }
                        _ => todo!(),
                    }
                })
            }
            VmirExprData::Val {
                linket_impl_or_val_path,
            } => ctx.eval_expr_itself(self, |ctx| match linket_impl_or_val_path {
                Left(linket_impl) => linket_impl.eval_vm(smallvec![], db),
                Right(val_path) => ctx.eval_val(val_path),
            }),
            VmirExprData::UnitTypeVariant { linket_impl } => {
                ctx.eval_expr_itself(self, |ctx| linket_impl.eval_vm(smallvec![], db))
            }
            VmirExprData::Unwrap { opd } => todo!(),
            VmirExprData::ConstTemplateVariable => todo!(),
            VmirExprData::RitchieItemPath => todo!(),
            VmirExprData::StaticVar { linket_impl } => todo!(),
        }?;
        VmControlFlow::Continue(match coercion {
            Some(coercion) => match coercion {
                VmirCoercion::Trivial => value,
                VmirCoercion::Never => todo!(),
                VmirCoercion::WrapInSome => todo!(),
                VmirCoercion::Redirection => {
                    // TODO
                    value
                }
                VmirCoercion::Dedirection => todo!(),
            },
            None => value,
        })
    }
}
