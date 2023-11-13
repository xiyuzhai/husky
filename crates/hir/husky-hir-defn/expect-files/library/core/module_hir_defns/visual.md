[
    HirDefn::MajorItem(
        MajorItemHirDefn::Trait(
            TraitHirDefn {
                path: TraitPath(`core::visual::Visualize`),
                hir_decl: TraitHirDecl {
                    path: TraitPath(`core::visual::Visualize`),
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                },
            },
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Type(
            TypeHirDefn::Extern(
                ExternTypeHirDefn {
                    path: TypePath(`core::visual::Html`, `Extern`),
                    hir_decl: ExternTypeHirDecl {
                        path: TypePath(`core::visual::Html`, `Extern`),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        hir_expr_region: HirEagerExprRegion {
                            hir_eager_expr_arena: Arena {
                                data: [],
                            },
                            hir_eager_stmt_arena: Arena {
                                data: [],
                            },
                            hir_eager_pattern_expr_arena: Arena {
                                data: [],
                            },
                            hir_eager_variable_region: HirEagerVariableRegion {
                                arena: Arena {
                                    data: [],
                                },
                                self_value_variable: None,
                            },
                        },
                    },
                },
            ),
        ),
    ),
    HirDefn::ImplBlock(
        ImplBlockHirDefn::TraitForType(
            TraitForTypeImplBlockHirDefn {
                hir_decl: TraitForTypeImplBlockHirDecl {
                    path: TraitForTypeImplBlockPath {
                        module_path: `core::visual`,
                        trai_path: TraitPath(`core::visual::Visualize`),
                        ty_sketch: TypeSketch::DeriveAny,
                        disambiguator: 0,
                    },
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                },
            },
        ),
    ),
    HirDefn::AssociatedItem(
        AssociatedItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::MethodFn(
                TraitForTypeMethodFnHirDefn {
                    path: TraitForTypeItemPath {
                        impl_block: TraitForTypeImplBlockPath {
                            module_path: `core::visual`,
                            trai_path: TraitPath(`core::visual::Visualize`),
                            ty_sketch: TypeSketch::DeriveAny,
                            disambiguator: 0,
                        },
                        ident: `visualize`,
                        item_kind: MethodFn,
                    },
                    hir_decl: TraitForTypeMethodFnHirDecl {
                        path: TraitForTypeItemPath {
                            impl_block: TraitForTypeImplBlockPath {
                                module_path: `core::visual`,
                                trai_path: TraitPath(`core::visual::Visualize`),
                                ty_sketch: TypeSketch::DeriveAny,
                                disambiguator: 0,
                            },
                            ident: `visualize`,
                            item_kind: MethodFn,
                        },
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        self_value_parameter: HirEagerSelfValueParameter,
                        parenate_parameters: HirEagerParenateParameters(
                            [],
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::visual::Html`, `Extern`),
                                template_arguments: [],
                            },
                        ),
                    },
                    eager_body_with_hir_eager_expr_region: None,
                },
            ),
        ),
    ),
]