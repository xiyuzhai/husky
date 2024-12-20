```rust
[
    (
        MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
        None,
    ),
    (
        MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
        Some(
            KiReprExpansion {
                path: ItemPath(`mnist_classifier::digits::zero::is_zero`),
                hir_lazy_variable_ki_repr_map: ArenaMap {
                    data: [
                        Some(
                            KiRepr(
                                Id {
                                    value: 377,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 400,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 410,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 440,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 448,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 454,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 456,
                                },
                            ),
                        ),
                        Some(
                            KiRepr(
                                Id {
                                    value: 462,
                                },
                            ),
                        ),
                    ],
                },
                hir_lazy_expr_ki_repr_map: [
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_connected_component`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 14,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 1,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `core::vec::Vec(0)::ilen`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`core::vec::Vec(0)::ilen`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [
                                            (
                                                HirTemplateVariable::Type(
                                                    HirTypeTemplateVariable::Type {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Mono,
                                                        },
                                                        variance: None,
                                                        disambiguator: 0,
                                                    },
                                                ),
                                                LinTermVariableResolution::Explicit(
                                                    LinTemplateArgument::Type(
                                                        LinType::PathLeading(
                                                            LinTypePathLeading {
                                                                ty_path: TypePath(`mnist_classifier::raw_contour::RawContour`, `Struct`),
                                                                template_arguments: [],
                                                            },
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ],
                                        separator: Some(
                                            1,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 372,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 2,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Literal(
                            Literal::I32(
                                1,
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 3,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Binary(
                            Comparison(
                                Eq,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 373,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 374,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 4,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::digits::zero::open_one_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ConditionSatisfied(
                            KiRepr(
                                Id {
                                    value: 375,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 370,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 6,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ConditionSatisfied(
                            KiRepr(
                                Id {
                                    value: 375,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 370,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 0,
                                variable_idx: 0,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ConditionSatisfied(
                            KiRepr(
                                Id {
                                    value: 375,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::F32(
                                F32Literal {
                                    value: 1.5,
                                    text: "1.5f32",
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 8,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ConditionSatisfied(
                            KiRepr(
                                Id {
                                    value: 375,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Comparison(
                                Less,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 377,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 379,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 9,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::digits::zero::open_one_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 381,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::StructField {
                                    self_ty: LinTypePathLeading {
                                        ty_path: TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                        template_arguments: [],
                                    },
                                    field_ty_leash_class: Other,
                                    field: Props {
                                        ident: `matches`,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 370,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 11,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 381,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::USize(
                                USizeLiteral {
                                    value: 0,
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 12,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 381,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 383,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 384,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 13,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::connected_components`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 387,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `core::vec::Vec(0)::ilen`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`core::vec::Vec(0)::ilen`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [
                                            (
                                                HirTemplateVariable::Type(
                                                    HirTypeTemplateVariable::Type {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Mono,
                                                        },
                                                        variance: None,
                                                        disambiguator: 0,
                                                    },
                                                ),
                                                LinTermVariableResolution::Explicit(
                                                    LinTemplateArgument::Type(
                                                        LinType::PathLeading(
                                                            LinTypePathLeading {
                                                                ty_path: TypePath(`mnist_classifier::connected_component::ConnectedComponent`, `Struct`),
                                                                template_arguments: [],
                                                            },
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ],
                                        separator: Some(
                                            1,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 389,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 15,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 387,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::I32(
                                1,
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 16,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 387,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Comparison(
                                Eq,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 390,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 391,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 17,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::digits::zero::open_one_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::StructField {
                                    self_ty: LinTypePathLeading {
                                        ty_path: TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                        template_arguments: [],
                                    },
                                    field_ty_leash_class: Other,
                                    field: Props {
                                        ident: `matches`,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 370,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 19,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::USize(
                                USizeLiteral {
                                    value: 0,
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 20,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 394,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 395,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 21,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Unwrap,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 396,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 22,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::displacement`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::displacement`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 397,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 23,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::Vector2d(0)::norm`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::Vector2d(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 398,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 24,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::Vector2d(0)::norm`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::Vector2d(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 398,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 4,
                                variable_idx: 1,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::F32(
                                F32Literal {
                                    value: 5.5,
                                    text: "5.5f32",
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 26,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Comparison(
                                Less,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 400,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 402,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 27,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 404,
                                },
                            ),
                        ),
                        opn: KiOpn::TypeVariant(
                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 28,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_concave_components`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::VecConstructor {
                                    element_ty: LinType::Ritchie(
                                        LinRitchieType {
                                            parameters: [
                                                LinRitchieParameter {
                                                    contract: Pure,
                                                    parameter_ty: PathLeading(
                                                        LinTypePathLeading(
                                                            Id {
                                                                value: 4,
                                                            },
                                                        ),
                                                    ),
                                                },
                                            ],
                                            return_ty: LinType::PathLeading(
                                                LinTypePathLeading {
                                                    ty_path: TypePath(`core::option::Option`, `Enum`),
                                                    template_arguments: [
                                                        LinTemplateArgument::Type(
                                                            LinType::PathLeading(
                                                                LinTypePathLeading {
                                                                    ty_path: TypePath(`core::num::f32`, `Extern`),
                                                                    template_arguments: [],
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                },
                                            ),
                                        },
                                    ),
                                },
                            },
                        ),
                        arguments: [
                            Variadic(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 31,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 32,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 8,
                                variable_idx: 2,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 410,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 35,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 8,
                                variable_idx: 2,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::rel_norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::rel_norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 410,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 37,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 8,
                                variable_idx: 2,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::angle_change_norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::angle_change_norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 410,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 39,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::I32(
                                5,
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 40,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                        Gn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`malamute::narrow_down`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [
                                                (
                                                    MajorItem(
                                                        Form(
                                                            MajorFormPath(
                                                                ItemPathId(
                                                                    Id {
                                                                        value: 116,
                                                                    },
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                    Type(
                                                        PathLeading(
                                                            LinTypePathLeading(
                                                                Id {
                                                                    value: 2,
                                                                },
                                                            ),
                                                        ),
                                                    ),
                                                ),
                                            ],
                                        },
                                        variable_resolutions: [
                                            (
                                                HirTemplateVariable::Type(
                                                    HirTypeTemplateVariable::Type {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Mono,
                                                        },
                                                        variance: None,
                                                        disambiguator: 0,
                                                    },
                                                ),
                                                LinTermVariableResolution::Explicit(
                                                    LinTemplateArgument::Type(
                                                        LinType::PathLeading(
                                                            LinTypePathLeading {
                                                                ty_path: TypePath(`mnist::MnistLabel`, `Enum`),
                                                                template_arguments: [],
                                                            },
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Variadic(
                                [
                                    KiRepr(
                                        Id {
                                            value: 411,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 412,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 413,
                                        },
                                    ),
                                ],
                            ),
                            Keyed(
                                Some(
                                    KiRepr(
                                        Id {
                                            value: 414,
                                        },
                                    ),
                                ),
                            ),
                            RuntimeConstants(
                                [
                                    KiRuntimeCompterm(
                                        Id {
                                            value: 3,
                                        },
                                    ),
                                ],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 41,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::UnveilAssocRitchie {
                                    path: TraitForTypeItemPath(
                                        `<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`,
                                        TraitItemKind::AssocRitchie(
                                            RitchieItemKind::Fn,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 415,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 42,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 8,
                                variable_idx: 2,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 416,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 410,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 44,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 416,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::F32(
                                F32Literal {
                                    value: 3.0,
                                    text: "3.0f32",
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 45,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 416,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Comparison(
                                Less,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 418,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 419,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 46,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_connected_component`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 14,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 48,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::StructField {
                                    self_ty: LinTypePathLeading {
                                        ty_path: TypePath(`mnist_classifier::connected_component::EffHoles`, `Struct`),
                                        template_arguments: [],
                                    },
                                    field_ty_leash_class: Other,
                                    field: Props {
                                        ident: `matches`,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 423,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 49,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::USize(
                                USizeLiteral {
                                    value: 1,
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 50,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 424,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 425,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 51,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_connected_component`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 14,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 53,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::StructField {
                                    self_ty: LinTypePathLeading {
                                        ty_path: TypePath(`mnist_classifier::connected_component::EffHoles`, `Struct`),
                                        template_arguments: [],
                                    },
                                    field_ty_leash_class: Other,
                                    field: Props {
                                        ident: `matches`,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 430,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 54,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::USize(
                                USizeLiteral {
                                    value: 0,
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 55,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 431,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 432,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 56,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_connected_component`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 14,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 58,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::StructField {
                                    self_ty: LinTypePathLeading {
                                        ty_path: TypePath(`mnist_classifier::connected_component::EffHoles`, `Struct`),
                                        template_arguments: [],
                                    },
                                    field_ty_leash_class: Other,
                                    field: Props {
                                        ident: `matches`,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 436,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 59,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::USize(
                                USizeLiteral {
                                    value: 0,
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 60,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 437,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 438,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 61,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 437,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 438,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 13,
                                variable_idx: 3,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Unwrap,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 440,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 63,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::raw_contour::RawContour(0)::bounding_box`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::raw_contour::RawContour(0)::bounding_box`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 441,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 64,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::BoundingBox(0)::ymax`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::BoundingBox(0)::ymax`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 442,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 65,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Index,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 437,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 438,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 13,
                                variable_idx: 3,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Unwrap,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 440,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 67,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::raw_contour::RawContour(0)::bounding_box`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::raw_contour::RawContour(0)::bounding_box`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 444,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 68,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::BoundingBox(0)::ymin`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::BoundingBox(0)::ymin`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 445,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 69,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Sub,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 443,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 446,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 70,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_line_segment_sketch`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::bounding_box`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::bounding_box`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 303,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 72,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::BoundingBox(0)::ymax`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::BoundingBox(0)::ymax`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 449,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 73,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorVal {
                                    path: MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::major::major_line_segment_sketch`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [],
                        source: KiReprSource::Val(
                            MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                        ),
                        caching_class: Val,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::bounding_box`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::bounding_box`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 303,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 75,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MethodRitchie {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::geom2d::BoundingBox(0)::ymin`,
                                            TypeItemKind::MethodRitchie(
                                                RitchieItemKind::Fn,
                                            ),
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::geom2d::BoundingBox(0)::ymin`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 451,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 76,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Sub,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 450,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 452,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 77,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Sub,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 443,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 446,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 14,
                                variable_idx: 4,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Sub,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 450,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 452,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 15,
                                variable_idx: 5,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Div,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 448,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 454,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 80,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Closed(
                                Div,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 448,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 454,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 16,
                                variable_idx: 6,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Literal(
                            Literal::F32(
                                F32Literal {
                                    value: 0.4,
                                    text: "0.4f32",
                                },
                            ),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 82,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Binary(
                            Comparison(
                                Greater,
                            ),
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 456,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 458,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 83,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::MajorRitchie {
                                    path: MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                        Fn,
                                    )`),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::fermi_match`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: None,
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 20,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 408,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: LetVariable {
                                stmt: 8,
                                variable_idx: 2,
                            },
                        },
                        caching_class: Variable,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 460,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::Memo {
                                    path: AssocItemPath::TypeItem(
                                        TypeItemPath(
                                            `mnist_classifier::fermi::FermiMatchResult(0)::norm`,
                                            TypeItemKind::MemoizedField,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`mnist_classifier::fermi::FermiMatchResult(0)::norm`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 410,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 85,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 460,
                                },
                            ),
                        ),
                        opn: KiOpn::TypeVariant(
                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 86,
                            },
                        },
                        caching_class: Expr,
                    },
                ],
                hir_lazy_stmt_ki_repr_map: [
                    KiRepr {
                        ki_domain_repr: ConditionSatisfied(
                            KiRepr(
                                Id {
                                    value: 375,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 380,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 378,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 1,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 381,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 386,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 382,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 2,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 387,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 392,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 388,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 3,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 393,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 403,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 401,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 5,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 404,
                                },
                            ),
                        ),
                        opn: KiOpn::Return,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 405,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 6,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Branches,
                        arguments: [
                            Branch {
                                condition: Some(
                                    KiRepr(
                                        Id {
                                            value: 375,
                                        },
                                    ),
                                ),
                                stmts: [
                                    KiRepr(
                                        Id {
                                            value: 381,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 387,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 393,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 404,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 406,
                                        },
                                    ),
                                ],
                            },
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 7,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 416,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 420,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 417,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 10,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 427,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 422,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 11,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 434,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 429,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 12,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 459,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 457,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 17,
                            },
                        },
                        caching_class: Stmt,
                    },
                ],
                root_hir_lazy_stmt_ki_reprs: [
                    KiRepr {
                        ki_domain_repr: Omni,
                        opn: KiOpn::Branches,
                        arguments: [
                            Branch {
                                condition: Some(
                                    KiRepr(
                                        Id {
                                            value: 375,
                                        },
                                    ),
                                ),
                                stmts: [
                                    KiRepr(
                                        Id {
                                            value: 381,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 387,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 393,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 404,
                                        },
                                    ),
                                    KiRepr(
                                        Id {
                                            value: 406,
                                        },
                                    ),
                                ],
                            },
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 7,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 407,
                                },
                            ),
                        ),
                        opn: KiOpn::Linket(
                            Linket {
                                data: LinketData::UnveilAssocRitchie {
                                    path: TraitForTypeItemPath(
                                        `<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`,
                                        TraitItemKind::AssocRitchie(
                                            RitchieItemKind::Fn,
                                        ),
                                    ),
                                    instantiation: LinInstantiation {
                                        path: ItemPath(`<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`),
                                        context: LinTypeContext {
                                            comptime_var_overrides: [],
                                        },
                                        variable_resolutions: [],
                                        separator: Some(
                                            0,
                                        ),
                                    },
                                },
                            },
                        ),
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 415,
                                    },
                                ),
                            ),
                            RuntimeConstants(
                                [],
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 42,
                            },
                        },
                        caching_class: Expr,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 416,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 420,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 417,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 10,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 421,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 427,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 422,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 11,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 428,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 434,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 429,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 12,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 435,
                                },
                            ),
                        ),
                        opn: KiOpn::Require,
                        arguments: [
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 459,
                                    },
                                ),
                            ),
                            Simple(
                                KiRepr(
                                    Id {
                                        value: 457,
                                    },
                                ),
                            ),
                        ],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Stmt {
                                stmt: 17,
                            },
                        },
                        caching_class: Stmt,
                    },
                    KiRepr {
                        ki_domain_repr: ControlNotTransferred(
                            KiRepr(
                                Id {
                                    value: 460,
                                },
                            ),
                        ),
                        opn: KiOpn::TypeVariant(
                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                        ),
                        arguments: [],
                        source: KiReprSource::Expansion {
                            parent_ki_repr: KiRepr {
                                ki_domain_repr: Omni,
                                opn: KiOpn::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                arguments: [],
                                source: KiReprSource::Val(
                                    MajorFormPath(`mnist_classifier::digits::zero::is_zero`, `Val`),
                                ),
                                caching_class: Val,
                            },
                            source: Expr {
                                expr: 86,
                            },
                        },
                        caching_class: Expr,
                    },
                ],
            },
        ),
    ),
]
```