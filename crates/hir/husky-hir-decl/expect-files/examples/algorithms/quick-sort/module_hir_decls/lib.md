[
    HirDecl::MajorItem(
        MajorItemHirDecl::Fugitive(
            FugitiveHirDecl::FunctionFn(
                FunctionFnFugitiveHirDecl {
                    path: FugitivePath(`quick_sort::quick_sort`, `FunctionFn`),
                    template_parameters: HirTemplateParameters(
                        [
                            HirTemplateParameter {
                                symbol: Type(
                                    Type {
                                        attrs: HirSymbolAttrs,
                                        variance: None,
                                        disambiguator: 0,
                                    },
                                ),
                                data: Type {
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 115,
                                            },
                                        ),
                                    ),
                                    traits: [],
                                },
                            },
                        ],
                    ),
                    parenate_parameters: HirEagerParenateParameters(
                        [
                            Ordinary {
                                pattern_expr_idx: 1,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 19,
                                        },
                                    ),
                                ),
                            },
                        ],
                    ),
                    return_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                            template_arguments: [],
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        hir_eager_expr_arena: Arena {
                            data: [],
                        },
                        hir_eager_stmt_arena: Arena {
                            data: [],
                        },
                        hir_eager_pattern_expr_arena: Arena {
                            data: [
                                Ident {
                                    symbol_modifier: Some(
                                        Mut,
                                    ),
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 193,
                                            },
                                        ),
                                    ),
                                },
                            ],
                        },
                        hir_eager_variable_region: HirEagerVariableRegion {
                            arena: Arena {
                                data: [
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 193,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                ],
                            },
                            self_value_variable: None,
                        },
                    },
                },
            ),
        ),
    ),
    HirDecl::MajorItem(
        MajorItemHirDecl::Fugitive(
            FugitiveHirDecl::FunctionFn(
                FunctionFnFugitiveHirDecl {
                    path: FugitivePath(`quick_sort::quick_sort_aux`, `FunctionFn`),
                    template_parameters: HirTemplateParameters(
                        [
                            HirTemplateParameter {
                                symbol: Type(
                                    Type {
                                        attrs: HirSymbolAttrs,
                                        variance: None,
                                        disambiguator: 0,
                                    },
                                ),
                                data: Type {
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 115,
                                            },
                                        ),
                                    ),
                                    traits: [],
                                },
                            },
                        ],
                    ),
                    parenate_parameters: HirEagerParenateParameters(
                        [
                            Ordinary {
                                pattern_expr_idx: 1,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 19,
                                        },
                                    ),
                                ),
                            },
                            Ordinary {
                                pattern_expr_idx: 2,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 8,
                                        },
                                    ),
                                ),
                            },
                            Ordinary {
                                pattern_expr_idx: 3,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 8,
                                        },
                                    ),
                                ),
                            },
                        ],
                    ),
                    return_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                            template_arguments: [],
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        hir_eager_expr_arena: Arena {
                            data: [],
                        },
                        hir_eager_stmt_arena: Arena {
                            data: [],
                        },
                        hir_eager_pattern_expr_arena: Arena {
                            data: [
                                Ident {
                                    symbol_modifier: Some(
                                        Mut,
                                    ),
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 193,
                                            },
                                        ),
                                    ),
                                },
                                Ident {
                                    symbol_modifier: None,
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 195,
                                            },
                                        ),
                                    ),
                                },
                                Ident {
                                    symbol_modifier: None,
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 196,
                                            },
                                        ),
                                    ),
                                },
                            ],
                        },
                        hir_eager_variable_region: HirEagerVariableRegion {
                            arena: Arena {
                                data: [
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 193,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 195,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 196,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                ],
                            },
                            self_value_variable: None,
                        },
                    },
                },
            ),
        ),
    ),
    HirDecl::MajorItem(
        MajorItemHirDecl::Fugitive(
            FugitiveHirDecl::FunctionFn(
                FunctionFnFugitiveHirDecl {
                    path: FugitivePath(`quick_sort::partition`, `FunctionFn`),
                    template_parameters: HirTemplateParameters(
                        [
                            HirTemplateParameter {
                                symbol: Type(
                                    Type {
                                        attrs: HirSymbolAttrs,
                                        variance: None,
                                        disambiguator: 0,
                                    },
                                ),
                                data: Type {
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 115,
                                            },
                                        ),
                                    ),
                                    traits: [],
                                },
                            },
                        ],
                    ),
                    parenate_parameters: HirEagerParenateParameters(
                        [
                            Ordinary {
                                pattern_expr_idx: 1,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 19,
                                        },
                                    ),
                                ),
                            },
                            Ordinary {
                                pattern_expr_idx: 2,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 8,
                                        },
                                    ),
                                ),
                            },
                            Ordinary {
                                pattern_expr_idx: 3,
                                ty: PathLeading(
                                    HirTypePathLeading(
                                        Id {
                                            value: 8,
                                        },
                                    ),
                                ),
                            },
                        ],
                    ),
                    return_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`core::num::isize`, `Extern`),
                            template_arguments: [],
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        hir_eager_expr_arena: Arena {
                            data: [],
                        },
                        hir_eager_stmt_arena: Arena {
                            data: [],
                        },
                        hir_eager_pattern_expr_arena: Arena {
                            data: [
                                Ident {
                                    symbol_modifier: Some(
                                        Mut,
                                    ),
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 193,
                                            },
                                        ),
                                    ),
                                },
                                Ident {
                                    symbol_modifier: None,
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 195,
                                            },
                                        ),
                                    ),
                                },
                                Ident {
                                    symbol_modifier: None,
                                    ident: Ident(
                                        Coword(
                                            Id {
                                                value: 196,
                                            },
                                        ),
                                    ),
                                },
                            ],
                        },
                        hir_eager_variable_region: HirEagerVariableRegion {
                            arena: Arena {
                                data: [
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 193,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 195,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                    HirEagerVariable {
                                        name: Ident(
                                            Ident(
                                                Coword(
                                                    Id {
                                                        value: 196,
                                                    },
                                                ),
                                            ),
                                        ),
                                        data: ParenateParameter,
                                    },
                                ],
                            },
                            self_value_variable: None,
                        },
                    },
                },
            ),
        ),
    ),
    HirDecl::MajorItem(
        MajorItemHirDecl::Fugitive(
            FugitiveHirDecl::FunctionFn(
                FunctionFnFugitiveHirDecl {
                    path: FugitivePath(`quick_sort::quick_sort_works_for_integers`, `FunctionFn`),
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                    parenate_parameters: HirEagerParenateParameters(
                        [],
                    ),
                    return_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                            template_arguments: [],
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
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
            ),
        ),
    ),
    HirDecl::MajorItem(
        MajorItemHirDecl::Fugitive(
            FugitiveHirDecl::FunctionFn(
                FunctionFnFugitiveHirDecl {
                    path: FugitivePath(`quick_sort::quick_sort_works_for_strs`, `FunctionFn`),
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                    parenate_parameters: HirEagerParenateParameters(
                        [],
                    ),
                    return_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                            template_arguments: [],
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
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
            ),
        ),
    ),
]