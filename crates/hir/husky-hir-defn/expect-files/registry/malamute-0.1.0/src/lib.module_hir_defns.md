```rust
[
    HirDefn::MajorItem(
        MajorItemHirDefn::Type(
            TypeHirDefn::Enum(
                EnumHirDefn {
                    path: TypePath(`malamute::Class`, `Enum`),
                    hir_decl: EnumHirDecl {
                        path: TypePath(`malamute::Class`, `Enum`),
                        template_parameters: HirTemplateParameters(
                            [
                                HirTemplateParameter {
                                    symbol: HirTemplateVariable::Type(
                                        HirTypeTemplateVariable::Type {
                                            attrs: HirTemplateVariableAttrs {
                                                class: Mono,
                                            },
                                            variance: None,
                                            disambiguator: 0,
                                        },
                                    ),
                                    data: HirTemplateParameterData::Type {
                                        ident: `Label`,
                                        traits: [],
                                    },
                                },
                            ],
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`malamute::Class`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerComptimeVariableEntry {
                                            name: HirEagerComptimeVariableName::Ident(
                                                `Label`,
                                            ),
                                            data: Current,
                                            hir_comptime_symbol: HirTemplateVariable::Type(
                                                HirTypeTemplateVariable::Type {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Mono,
                                                    },
                                                    variance: None,
                                                    disambiguator: 0,
                                                },
                                            ),
                                        },
                                    ],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Tuple(
            EnumTupleVariantHirDefn {
                path: TypeVariantPath(`malamute::Class::Known`),
                hir_decl: EnumTupleVariantHirDecl {
                    path: TypeVariantPath(`malamute::Class::Known`),
                    fields: [
                        EnumTupleVariantField {
                            ty: HirType::Variable(
                                HirTypeTemplateVariable::Type {
                                    attrs: HirTemplateVariableAttrs {
                                        class: Mono,
                                    },
                                    variance: None,
                                    disambiguator: 0,
                                },
                            ),
                        },
                    ],
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::Class::Known`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [
                                    HirEagerComptimeVariableEntry {
                                        name: HirEagerComptimeVariableName::Ident(
                                            `Label`,
                                        ),
                                        data: Inherited,
                                        hir_comptime_symbol: HirTemplateVariable::Type(
                                            HirTypeTemplateVariable::Type {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Mono,
                                                },
                                                variance: None,
                                                disambiguator: 0,
                                            },
                                        ),
                                    },
                                ],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::Class::Unknown`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::Class::Unknown`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::Class::Unknown`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [
                                    HirEagerComptimeVariableEntry {
                                        name: HirEagerComptimeVariableName::Ident(
                                            `Label`,
                                        ),
                                        data: Inherited,
                                        hir_comptime_symbol: HirTemplateVariable::Type(
                                            HirTypeTemplateVariable::Type {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Mono,
                                                },
                                                variance: None,
                                                disambiguator: 0,
                                            },
                                        ),
                                    },
                                ],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::MajorItem(
        MajorItemHirDefn::Type(
            TypeHirDefn::Enum(
                EnumHirDefn {
                    path: TypePath(`malamute::OneVsAll`, `Enum`),
                    hir_decl: EnumHirDecl {
                        path: TypePath(`malamute::OneVsAll`, `Enum`),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`malamute::OneVsAll`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::OneVsAll::Yes`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::OneVsAll::Yes`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAll::Yes`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::OneVsAll::No`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::OneVsAll::No`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAll::No`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::MajorItem(
        MajorItemHirDefn::Type(
            TypeHirDefn::Enum(
                EnumHirDefn {
                    path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                    hir_decl: EnumHirDecl {
                        path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`malamute::OneVsAllResult`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::OneVsAllResult::ConfidentYes`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::OneVsAllResult::ConfidentYes`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAllResult::ConfidentYes`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::OneVsAllResult::ConfidentNo`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::OneVsAllResult::ConfidentNo`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAllResult::ConfidentNo`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::TypeVariant(
        TypeVariantHirDefn::Unit(
            EnumUnitVariantHirDefn {
                path: TypeVariantPath(`malamute::OneVsAllResult::Unconfident`),
                hir_decl: EnumUnitTypeVariantHirDecl {
                    path: TypeVariantPath(`malamute::OneVsAllResult::Unconfident`),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAllResult::Unconfident`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::MajorItem(
        MajorItemHirDefn::Form(
            MajorFormHirDefn::Ritchie(
                MajorFunctionRitchieHirDefn {
                    path: MajorFormPath(`malamute::narrow_down`, `Ritchie(
                        Gn,
                    )`),
                    hir_decl: MajorFunctionRitchieHirDecl {
                        path: MajorFormPath(`malamute::narrow_down`, `Ritchie(
                            Gn,
                        )`),
                        ritchie_item_kind: RitchieItemKind::Gn,
                        template_parameters: HirTemplateParameters(
                            [
                                HirTemplateParameter {
                                    symbol: HirTemplateVariable::Type(
                                        HirTypeTemplateVariable::Type {
                                            attrs: HirTemplateVariableAttrs {
                                                class: Mono,
                                            },
                                            variance: None,
                                            disambiguator: 0,
                                        },
                                    ),
                                    data: HirTemplateParameterData::Type {
                                        ident: `Label`,
                                        traits: [],
                                    },
                                },
                                HirTemplateParameter {
                                    symbol: HirTemplateVariable::Compterm(
                                        HirComptermTemplateVariable {
                                            ty: HirType::Variable(
                                                HirTypeTemplateVariable::Type {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Mono,
                                                    },
                                                    variance: None,
                                                    disambiguator: 0,
                                                },
                                            ),
                                            index: HirComptermTemplateVariableIndex::Other {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Poly,
                                                },
                                                disambiguator: 0,
                                            },
                                        },
                                    ),
                                    data: HirTemplateParameterData::Constant {
                                        ident: `label`,
                                        ty: HirType::Variable(
                                            HirTypeTemplateVariable::Type {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Mono,
                                                },
                                                variance: None,
                                                disambiguator: 0,
                                            },
                                        ),
                                    },
                                },
                            ],
                        ),
                        parenate_parameters: HirParenateParameters::Lazy(
                            HirLazyParenateParameters(
                                [
                                    Variadic {
                                        variant: Vec,
                                        ty: PathLeading(
                                            HirTypePathLeading(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    },
                                    Keyed {
                                        ident: `skip`,
                                        ty: PathLeading(
                                            HirTypePathLeading(
                                                Id {
                                                    value: 3,
                                                },
                                            ),
                                        ),
                                    },
                                ],
                            ),
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                                template_arguments: [],
                                always_copyable: true,
                            },
                        ),
                        hir_expr_region: Lazy(
                            HirLazyExprRegion(
                                Id {
                                    value: 1,
                                },
                            ),
                        ),
                    },
                    body_with_hir_expr_region: None,
                },
            ),
        ),
    ),
    HirDefn::ImplBlock(
        ImplBlockHirDefn::TraitForType(
            TraitForTypeImplBlockHirDefn {
                hir_decl: TraitForTypeImplBlockHirDecl {
                    path: TraitForTypeImplBlockPath(`malamute::OneVsAll as core::default::Default(0)`),
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                    trai: HirTrait {
                        trai_path: TraitPath(`core::default::Default`),
                        template_arguments: [],
                    },
                    self_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                            template_arguments: [],
                            always_copyable: true,
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAll as core::default::Default(0)`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::AssocItem(
        AssocItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::AssocRitchie(
                TraitForTypeAssocRitchieHirDefn {
                    path: TraitForTypeItemPath(
                        `<malamute::OneVsAll as core::default::Default(0)>::default`,
                        TraitItemKind::AssocRitchie(
                            RitchieItemKind::Fn,
                        ),
                    ),
                    hir_decl: TraitForTypeAssocRitchieHirDecl {
                        path: TraitForTypeItemPath(
                            `<malamute::OneVsAll as core::default::Default(0)>::default`,
                            TraitItemKind::AssocRitchie(
                                RitchieItemKind::Fn,
                            ),
                        ),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        parenate_parameters: HirEagerParenateParameters(
                            [],
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                template_arguments: [],
                                always_copyable: true,
                            },
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`<malamute::OneVsAll as core::default::Default(0)>::default`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerRuntimeVariableEntry {
                                            name: HirEagerRuntimeVariableName::SelfValue,
                                            data: HirEagerRuntimeVariableData::SelfValue,
                                        },
                                    ],
                                },
                                self_value_variable: Some(
                                    0,
                                ),
                            },
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            1,
                            HirEagerExprRegion {
                                region_path: RegionPath::ItemDefn(
                                    ItemPath(`<malamute::OneVsAll as core::default::Default(0)>::default`),
                                ),
                                self_value_ty: None,
                                expr_arena: Arena {
                                    data: [
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::PrincipalEntityPath {
                                                path: PrincipalEntityPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAll::No`),
                                                ),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`malamute::OneVsAll::No`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [],
                                                    separator: None,
                                                },
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::Block {
                                                stmts: ArenaIdxRange(
                                                    0..1,
                                                ),
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Eval {
                                            expr: 0,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                    ],
                                },
                                pattern_arena: Arena {
                                    data: [],
                                },
                                comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                    arena: Arena {
                                        data: [],
                                    },
                                },
                                runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                    arena: Arena {
                                        data: [],
                                    },
                                    self_value_variable: None,
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::ImplBlock(
        ImplBlockHirDefn::TraitForType(
            TraitForTypeImplBlockHirDefn {
                hir_decl: TraitForTypeImplBlockHirDecl {
                    path: TraitForTypeImplBlockPath(`malamute::Class as core::ops::Unveil(0)`),
                    template_parameters: HirTemplateParameters(
                        [
                            HirTemplateParameter {
                                symbol: HirTemplateVariable::Type(
                                    HirTypeTemplateVariable::Type {
                                        attrs: HirTemplateVariableAttrs {
                                            class: Mono,
                                        },
                                        variance: None,
                                        disambiguator: 0,
                                    },
                                ),
                                data: HirTemplateParameterData::Type {
                                    ident: `Label`,
                                    traits: [],
                                },
                            },
                            HirTemplateParameter {
                                symbol: HirTemplateVariable::Compterm(
                                    HirComptermTemplateVariable {
                                        ty: HirType::Variable(
                                            HirTypeTemplateVariable::Type {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Mono,
                                                },
                                                variance: None,
                                                disambiguator: 0,
                                            },
                                        ),
                                        index: HirComptermTemplateVariableIndex::Other {
                                            attrs: HirTemplateVariableAttrs {
                                                class: Poly,
                                            },
                                            disambiguator: 0,
                                        },
                                    },
                                ),
                                data: HirTemplateParameterData::Constant {
                                    ident: `label`,
                                    ty: HirType::Variable(
                                        HirTypeTemplateVariable::Type {
                                            attrs: HirTemplateVariableAttrs {
                                                class: Mono,
                                            },
                                            variance: None,
                                            disambiguator: 0,
                                        },
                                    ),
                                },
                            },
                        ],
                    ),
                    trai: HirTrait {
                        trai_path: TraitPath(`core::ops::Unveil`),
                        template_arguments: [
                            HirTemplateArgument::Type(
                                HirType::PathLeading(
                                    HirTypePathLeading {
                                        ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                        template_arguments: [],
                                        always_copyable: true,
                                    },
                                ),
                            ),
                        ],
                    },
                    self_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`malamute::Class`, `Enum`),
                            template_arguments: [
                                HirTemplateArgument::Type(
                                    HirType::Variable(
                                        HirTypeTemplateVariable::Type {
                                            attrs: HirTemplateVariableAttrs {
                                                class: Mono,
                                            },
                                            variance: None,
                                            disambiguator: 0,
                                        },
                                    ),
                                ),
                            ],
                            always_copyable: true,
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::Class as core::ops::Unveil(0)`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [
                                    HirEagerComptimeVariableEntry {
                                        name: HirEagerComptimeVariableName::Ident(
                                            `Label`,
                                        ),
                                        data: Current,
                                        hir_comptime_symbol: HirTemplateVariable::Type(
                                            HirTypeTemplateVariable::Type {
                                                attrs: HirTemplateVariableAttrs {
                                                    class: Mono,
                                                },
                                                variance: None,
                                                disambiguator: 0,
                                            },
                                        ),
                                    },
                                    HirEagerComptimeVariableEntry {
                                        name: HirEagerComptimeVariableName::Ident(
                                            `label`,
                                        ),
                                        data: Current,
                                        hir_comptime_symbol: HirTemplateVariable::Compterm(
                                            HirComptermTemplateVariable {
                                                ty: HirType::Variable(
                                                    HirTypeTemplateVariable::Type {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Mono,
                                                        },
                                                        variance: None,
                                                        disambiguator: 0,
                                                    },
                                                ),
                                                index: HirComptermTemplateVariableIndex::Other {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Poly,
                                                    },
                                                    disambiguator: 0,
                                                },
                                            },
                                        ),
                                    },
                                ],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::AssocItem(
        AssocItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::AssocType(
                TraitForTypeAssocTypeHirDefn {
                    path: TraitForTypeItemPath(
                        `<malamute::Class as core::ops::Unveil(0)>::Output`,
                        TraitItemKind::AssocType,
                    ),
                    hir_decl: TraitForTypeAssocTypeHirDecl {
                        path: TraitForTypeItemPath(
                            `<malamute::Class as core::ops::Unveil(0)>::Output`,
                            TraitItemKind::AssocType,
                        ),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::basic::unit`, `Extern`),
                                template_arguments: [],
                                always_copyable: true,
                            },
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`<malamute::Class as core::ops::Unveil(0)>::Output`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerComptimeVariableEntry {
                                            name: HirEagerComptimeVariableName::Ident(
                                                `Label`,
                                            ),
                                            data: Inherited,
                                            hir_comptime_symbol: HirTemplateVariable::Type(
                                                HirTypeTemplateVariable::Type {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Mono,
                                                    },
                                                    variance: None,
                                                    disambiguator: 0,
                                                },
                                            ),
                                        },
                                        HirEagerComptimeVariableEntry {
                                            name: HirEagerComptimeVariableName::Ident(
                                                `label`,
                                            ),
                                            data: Inherited,
                                            hir_comptime_symbol: HirTemplateVariable::Compterm(
                                                HirComptermTemplateVariable {
                                                    ty: HirType::Variable(
                                                        HirTypeTemplateVariable::Type {
                                                            attrs: HirTemplateVariableAttrs {
                                                                class: Mono,
                                                            },
                                                            variance: None,
                                                            disambiguator: 0,
                                                        },
                                                    ),
                                                    index: HirComptermTemplateVariableIndex::Other {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Poly,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        },
                                    ],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::AssocItem(
        AssocItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::AssocRitchie(
                TraitForTypeAssocRitchieHirDefn {
                    path: TraitForTypeItemPath(
                        `<malamute::Class as core::ops::Unveil(0)>::unveil`,
                        TraitItemKind::AssocRitchie(
                            RitchieItemKind::Fn,
                        ),
                    ),
                    hir_decl: TraitForTypeAssocRitchieHirDecl {
                        path: TraitForTypeItemPath(
                            `<malamute::Class as core::ops::Unveil(0)>::unveil`,
                            TraitItemKind::AssocRitchie(
                                RitchieItemKind::Fn,
                            ),
                        ),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        parenate_parameters: HirEagerParenateParameters(
                            [
                                HirEagerParenateParameter::Simple {
                                    pattern_idx: 0,
                                    contract: Pure,
                                    ty: HirType::PathLeading(
                                        HirTypePathLeading {
                                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                            template_arguments: [],
                                            always_copyable: true,
                                        },
                                    ),
                                },
                            ],
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                template_arguments: [
                                    HirTemplateArgument::Type(
                                        HirType::PathLeading(
                                            HirTypePathLeading {
                                                ty_path: TypePath(`malamute::Class`, `Enum`),
                                                template_arguments: [
                                                    HirTemplateArgument::Type(
                                                        HirType::Variable(
                                                            HirTypeTemplateVariable::Type {
                                                                attrs: HirTemplateVariableAttrs {
                                                                    class: Mono,
                                                                },
                                                                variance: None,
                                                                disambiguator: 0,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                                always_copyable: true,
                                            },
                                        ),
                                    ),
                                    HirTemplateArgument::Type(
                                        HirType::PathLeading(
                                            HirTypePathLeading {
                                                ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                template_arguments: [],
                                                always_copyable: true,
                                            },
                                        ),
                                    ),
                                ],
                                always_copyable: false,
                            },
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`<malamute::Class as core::ops::Unveil(0)>::unveil`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [
                                    HirEagerPatternEntry {
                                        data: HirEagerPatternData::Ident {
                                            symbol_modifier: None,
                                            ident: `one_vs_all`,
                                            variable_idx: 1,
                                        },
                                        contract: Pure,
                                    },
                                ],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerComptimeVariableEntry {
                                            name: HirEagerComptimeVariableName::Ident(
                                                `Label`,
                                            ),
                                            data: Inherited,
                                            hir_comptime_symbol: HirTemplateVariable::Type(
                                                HirTypeTemplateVariable::Type {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Mono,
                                                    },
                                                    variance: None,
                                                    disambiguator: 0,
                                                },
                                            ),
                                        },
                                        HirEagerComptimeVariableEntry {
                                            name: HirEagerComptimeVariableName::Ident(
                                                `label`,
                                            ),
                                            data: Inherited,
                                            hir_comptime_symbol: HirTemplateVariable::Compterm(
                                                HirComptermTemplateVariable {
                                                    ty: HirType::Variable(
                                                        HirTypeTemplateVariable::Type {
                                                            attrs: HirTemplateVariableAttrs {
                                                                class: Mono,
                                                            },
                                                            variance: None,
                                                            disambiguator: 0,
                                                        },
                                                    ),
                                                    index: HirComptermTemplateVariableIndex::Other {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Poly,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        },
                                    ],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerRuntimeVariableEntry {
                                            name: HirEagerRuntimeVariableName::SelfValue,
                                            data: HirEagerRuntimeVariableData::SelfValue,
                                        },
                                        HirEagerRuntimeVariableEntry {
                                            name: HirEagerRuntimeVariableName::Ident(
                                                `one_vs_all`,
                                            ),
                                            data: HirEagerRuntimeVariableData::ParenateParameter,
                                        },
                                    ],
                                },
                                self_value_variable: Some(
                                    0,
                                ),
                            },
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            6,
                            HirEagerExprRegion {
                                region_path: RegionPath::ItemDefn(
                                    ItemPath(`<malamute::Class as core::ops::Unveil(0)>::unveil`),
                                ),
                                self_value_ty: None,
                                expr_arena: Arena {
                                    data: [
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::RuntimeVariable(
                                                0,
                                            ),
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: Some(
                                                    Pure,
                                                ),
                                                quary: StackPure {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [
                                                    (
                                                        Idx(
                                                            PlaceIdx(0),
                                                        ),
                                                        Pure,
                                                    ),
                                                ],
                                            },
                                            coercion: None,
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: Some(
                                                    Pure,
                                                ),
                                                quary: StackPure {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::ComptimeVariable {
                                                ident: `label`,
                                            },
                                            base_ty: HirType::Variable(
                                                HirTypeTemplateVariable::Type {
                                                    attrs: HirTemplateVariableAttrs {
                                                        class: Mono,
                                                    },
                                                    variance: None,
                                                    disambiguator: 0,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Compterm,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Compterm,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Compterm,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`malamute::Class::Known`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`malamute::Class::Known`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::Variable(
                                                                        HirTypeTemplateVariable::Type {
                                                                            attrs: HirTemplateVariableAttrs {
                                                                                class: Mono,
                                                                            },
                                                                            variance: None,
                                                                            disambiguator: 0,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: Variable(
                                                                Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 0,
                                                                },
                                                            ),
                                                        },
                                                        1,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Compterm,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::Class`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::Variable(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 0,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`core::ops::ControlFlow::Break`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`core::ops::ControlFlow::Break`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`malamute::Class`, `Enum`),
                                                                            template_arguments: [
                                                                                HirTemplateArgument::Type(
                                                                                    HirType::Variable(
                                                                                        HirTypeTemplateVariable::Type {
                                                                                            attrs: HirTemplateVariableAttrs {
                                                                                                class: Mono,
                                                                                            },
                                                                                            variance: None,
                                                                                            disambiguator: 0,
                                                                                        },
                                                                                    ),
                                                                                ),
                                                                            ],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                        (
                                                            HirTemplateVariable::Type(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 1,
                                                                },
                                                            ),
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: PathLeading(
                                                                HirTypePathLeading(
                                                                    Id {
                                                                        value: 6,
                                                                    },
                                                                ),
                                                            ),
                                                        },
                                                        2,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::Class`, `Enum`),
                                                                    template_arguments: [
                                                                        HirTemplateArgument::Type(
                                                                            HirType::Variable(
                                                                                HirTypeTemplateVariable::Type {
                                                                                    attrs: HirTemplateVariableAttrs {
                                                                                        class: Mono,
                                                                                    },
                                                                                    variance: None,
                                                                                    disambiguator: 0,
                                                                                },
                                                                            ),
                                                                        ),
                                                                    ],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::Literal(
                                                Literal::Unit(
                                                    (),
                                                ),
                                            ),
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`core::ops::ControlFlow::Continue`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`core::ops::ControlFlow::Continue`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`malamute::Class`, `Enum`),
                                                                            template_arguments: [
                                                                                HirTemplateArgument::Type(
                                                                                    HirType::Variable(
                                                                                        HirTypeTemplateVariable::Type {
                                                                                            attrs: HirTemplateVariableAttrs {
                                                                                                class: Mono,
                                                                                            },
                                                                                            variance: None,
                                                                                            disambiguator: 0,
                                                                                        },
                                                                                    ),
                                                                                ),
                                                                            ],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                        (
                                                            HirTemplateVariable::Type(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 1,
                                                                },
                                                            ),
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: PathLeading(
                                                                HirTypePathLeading(
                                                                    Id {
                                                                        value: 1,
                                                                    },
                                                                ),
                                                            ),
                                                        },
                                                        4,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::Class`, `Enum`),
                                                                    template_arguments: [
                                                                        HirTemplateArgument::Type(
                                                                            HirType::Variable(
                                                                                HirTypeTemplateVariable::Type {
                                                                                    attrs: HirTemplateVariableAttrs {
                                                                                        class: Mono,
                                                                                    },
                                                                                    variance: None,
                                                                                    disambiguator: 0,
                                                                                },
                                                                            ),
                                                                        ),
                                                                    ],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::Block {
                                                stmts: ArenaIdxRange(
                                                    2..3,
                                                ),
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::Class`, `Enum`),
                                                                    template_arguments: [
                                                                        HirTemplateArgument::Type(
                                                                            HirType::Variable(
                                                                                HirTypeTemplateVariable::Type {
                                                                                    attrs: HirTemplateVariableAttrs {
                                                                                        class: Mono,
                                                                                    },
                                                                                    variance: None,
                                                                                    disambiguator: 0,
                                                                                },
                                                                            ),
                                                                        ),
                                                                    ],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Eval {
                                            expr: 3,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                        Eval {
                                            expr: 5,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                        Match {
                                            opd: 0,
                                            contract: Pure,
                                            case_branches: [
                                                HirEagerCaseBranch {
                                                    pattern: 0,
                                                    stmts: ArenaIdxRange(
                                                        0..1,
                                                    ),
                                                },
                                                HirEagerCaseBranch {
                                                    pattern: 1,
                                                    stmts: ArenaIdxRange(
                                                        1..2,
                                                    ),
                                                },
                                            ],
                                        },
                                    ],
                                },
                                pattern_arena: Arena {
                                    data: [
                                        HirEagerPatternEntry {
                                            data: HirEagerPatternData::UnitPath(
                                                PatternPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAll::Yes`),
                                                ),
                                            ),
                                            contract: Pure,
                                        },
                                        HirEagerPatternEntry {
                                            data: HirEagerPatternData::UnitPath(
                                                PatternPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAll::No`),
                                                ),
                                            ),
                                            contract: Pure,
                                        },
                                    ],
                                },
                                comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                    arena: Arena {
                                        data: [
                                            HirEagerComptimeVariableEntry {
                                                name: HirEagerComptimeVariableName::Ident(
                                                    `Label`,
                                                ),
                                                data: Inherited,
                                                hir_comptime_symbol: HirTemplateVariable::Type(
                                                    HirTypeTemplateVariable::Type {
                                                        attrs: HirTemplateVariableAttrs {
                                                            class: Mono,
                                                        },
                                                        variance: None,
                                                        disambiguator: 0,
                                                    },
                                                ),
                                            },
                                            HirEagerComptimeVariableEntry {
                                                name: HirEagerComptimeVariableName::Ident(
                                                    `label`,
                                                ),
                                                data: Inherited,
                                                hir_comptime_symbol: HirTemplateVariable::Compterm(
                                                    HirComptermTemplateVariable {
                                                        ty: HirType::Variable(
                                                            HirTypeTemplateVariable::Type {
                                                                attrs: HirTemplateVariableAttrs {
                                                                    class: Mono,
                                                                },
                                                                variance: None,
                                                                disambiguator: 0,
                                                            },
                                                        ),
                                                        index: HirComptermTemplateVariableIndex::Other {
                                                            attrs: HirTemplateVariableAttrs {
                                                                class: Poly,
                                                            },
                                                            disambiguator: 0,
                                                        },
                                                    },
                                                ),
                                            },
                                        ],
                                    },
                                },
                                runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                    arena: Arena {
                                        data: [
                                            HirEagerRuntimeVariableEntry {
                                                name: HirEagerRuntimeVariableName::Ident(
                                                    `one_vs_all`,
                                                ),
                                                data: HirEagerRuntimeVariableData::ParenateParameter,
                                            },
                                        ],
                                    },
                                    self_value_variable: None,
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::ImplBlock(
        ImplBlockHirDefn::TraitForType(
            TraitForTypeImplBlockHirDefn {
                hir_decl: TraitForTypeImplBlockHirDecl {
                    path: TraitForTypeImplBlockPath(`malamute::OneVsAll as core::ops::Unveil(0)`),
                    template_parameters: HirTemplateParameters(
                        [],
                    ),
                    trai: HirTrait {
                        trai_path: TraitPath(`core::ops::Unveil`),
                        template_arguments: [
                            HirTemplateArgument::Type(
                                HirType::PathLeading(
                                    HirTypePathLeading {
                                        ty_path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                                        template_arguments: [],
                                        always_copyable: true,
                                    },
                                ),
                            ),
                        ],
                    },
                    self_ty: HirType::PathLeading(
                        HirTypePathLeading {
                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                            template_arguments: [],
                            always_copyable: true,
                        },
                    ),
                    hir_eager_expr_region: HirEagerExprRegion {
                        region_path: RegionPath::ItemDecl(
                            ItemPath(`malamute::OneVsAll as core::ops::Unveil(0)`),
                        ),
                        self_value_ty: None,
                        expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [],
                        },
                        pattern_arena: Arena {
                            data: [],
                        },
                        comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                            arena: Arena {
                                data: [],
                            },
                        },
                        runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::AssocItem(
        AssocItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::AssocType(
                TraitForTypeAssocTypeHirDefn {
                    path: TraitForTypeItemPath(
                        `<malamute::OneVsAll as core::ops::Unveil(0)>::Output`,
                        TraitItemKind::AssocType,
                    ),
                    hir_decl: TraitForTypeAssocTypeHirDecl {
                        path: TraitForTypeItemPath(
                            `<malamute::OneVsAll as core::ops::Unveil(0)>::Output`,
                            TraitItemKind::AssocType,
                        ),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::basic::unit`, `Extern`),
                                template_arguments: [],
                                always_copyable: true,
                            },
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`<malamute::OneVsAll as core::ops::Unveil(0)>::Output`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
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
    HirDefn::AssocItem(
        AssocItemHirDefn::TraitForTypeItem(
            TraitForTypeItemHirDefn::AssocRitchie(
                TraitForTypeAssocRitchieHirDefn {
                    path: TraitForTypeItemPath(
                        `<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`,
                        TraitItemKind::AssocRitchie(
                            RitchieItemKind::Fn,
                        ),
                    ),
                    hir_decl: TraitForTypeAssocRitchieHirDecl {
                        path: TraitForTypeItemPath(
                            `<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`,
                            TraitItemKind::AssocRitchie(
                                RitchieItemKind::Fn,
                            ),
                        ),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        parenate_parameters: HirEagerParenateParameters(
                            [
                                HirEagerParenateParameter::Simple {
                                    pattern_idx: 0,
                                    contract: Pure,
                                    ty: HirType::PathLeading(
                                        HirTypePathLeading {
                                            ty_path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                                            template_arguments: [],
                                            always_copyable: true,
                                        },
                                    ),
                                },
                            ],
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                template_arguments: [
                                    HirTemplateArgument::Type(
                                        HirType::PathLeading(
                                            HirTypePathLeading {
                                                ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                template_arguments: [],
                                                always_copyable: true,
                                            },
                                        ),
                                    ),
                                    HirTemplateArgument::Type(
                                        HirType::PathLeading(
                                            HirTypePathLeading {
                                                ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                template_arguments: [],
                                                always_copyable: true,
                                            },
                                        ),
                                    ),
                                ],
                                always_copyable: false,
                            },
                        ),
                        hir_eager_expr_region: HirEagerExprRegion {
                            region_path: RegionPath::ItemDecl(
                                ItemPath(`<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`),
                            ),
                            self_value_ty: None,
                            expr_arena: Arena {
                                data: [],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_arena: Arena {
                                data: [
                                    HirEagerPatternEntry {
                                        data: HirEagerPatternData::Ident {
                                            symbol_modifier: None,
                                            ident: `one_vs_all_result`,
                                            variable_idx: 1,
                                        },
                                        contract: Pure,
                                    },
                                ],
                            },
                            comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                arena: Arena {
                                    data: [],
                                },
                            },
                            runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                arena: Arena {
                                    data: [
                                        HirEagerRuntimeVariableEntry {
                                            name: HirEagerRuntimeVariableName::SelfValue,
                                            data: HirEagerRuntimeVariableData::SelfValue,
                                        },
                                        HirEagerRuntimeVariableEntry {
                                            name: HirEagerRuntimeVariableName::Ident(
                                                `one_vs_all_result`,
                                            ),
                                            data: HirEagerRuntimeVariableData::ParenateParameter,
                                        },
                                    ],
                                },
                                self_value_variable: Some(
                                    0,
                                ),
                            },
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            7,
                            HirEagerExprRegion {
                                region_path: RegionPath::ItemDefn(
                                    ItemPath(`<malamute::OneVsAll as core::ops::Unveil(0)>::unveil`),
                                ),
                                self_value_ty: None,
                                expr_arena: Arena {
                                    data: [
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::RuntimeVariable(
                                                0,
                                            ),
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAllResult`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: Some(
                                                    Pure,
                                                ),
                                                quary: StackPure {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [
                                                    (
                                                        Idx(
                                                            PlaceIdx(0),
                                                        ),
                                                        Pure,
                                                    ),
                                                ],
                                            },
                                            coercion: None,
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: Some(
                                                    Pure,
                                                ),
                                                quary: StackPure {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::PrincipalEntityPath {
                                                path: PrincipalEntityPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAll::Yes`),
                                                ),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`malamute::OneVsAll::Yes`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [],
                                                    separator: None,
                                                },
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`core::ops::ControlFlow::Break`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`core::ops::ControlFlow::Break`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                        (
                                                            HirTemplateVariable::Type(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 1,
                                                                },
                                                            ),
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: PathLeading(
                                                                HirTypePathLeading(
                                                                    Id {
                                                                        value: 5,
                                                                    },
                                                                ),
                                                            ),
                                                        },
                                                        1,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::PrincipalEntityPath {
                                                path: PrincipalEntityPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAll::No`),
                                                ),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`malamute::OneVsAll::No`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [],
                                                    separator: None,
                                                },
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`core::ops::ControlFlow::Break`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`core::ops::ControlFlow::Break`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                        (
                                                            HirTemplateVariable::Type(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 1,
                                                                },
                                                            ),
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: PathLeading(
                                                                HirTypePathLeading(
                                                                    Id {
                                                                        value: 5,
                                                                    },
                                                                ),
                                                            ),
                                                        },
                                                        3,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::Literal(
                                                Literal::Unit(
                                                    (),
                                                ),
                                            ),
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                    template_arguments: [],
                                                    always_copyable: true,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: true,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::TypeVariantConstructorCall {
                                                path: TypeVariantPath(`core::ops::ControlFlow::Continue`),
                                                instantiation: HirInstantiation {
                                                    path: ItemPath(`core::ops::ControlFlow::Continue`),
                                                    context: HirTypeContext {
                                                        comptime_var_overrides: [],
                                                    },
                                                    variable_map: [
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
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                        (
                                                            HirTemplateVariable::Type(
                                                                HirTypeTemplateVariable::Type {
                                                                    attrs: HirTemplateVariableAttrs {
                                                                        class: Mono,
                                                                    },
                                                                    variance: None,
                                                                    disambiguator: 1,
                                                                },
                                                            ),
                                                            HirTermSymbolicVariableResolution::Explicit(
                                                                HirTemplateArgument::Type(
                                                                    HirType::PathLeading(
                                                                        HirTypePathLeading {
                                                                            ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                            template_arguments: [],
                                                                            always_copyable: true,
                                                                        },
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ],
                                                    separator: None,
                                                },
                                                arguments: [
                                                    Simple(
                                                        HirRitchieSimpleParameter {
                                                            contract: Move,
                                                            ty: PathLeading(
                                                                HirTypePathLeading(
                                                                    Id {
                                                                        value: 1,
                                                                    },
                                                                ),
                                                            ),
                                                        },
                                                        5,
                                                        Trivial(
                                                            TrivialHirEagerCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    ),
                                                ],
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                        HirEagerExprEntry {
                                            data: HirEagerExprData::Block {
                                                stmts: ArenaIdxRange(
                                                    3..4,
                                                ),
                                            },
                                            base_ty: HirType::PathLeading(
                                                HirTypePathLeading {
                                                    ty_path: TypePath(`core::ops::ControlFlow`, `Enum`),
                                                    template_arguments: [
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`malamute::OneVsAll`, `Enum`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                        HirTemplateArgument::Type(
                                                            HirType::PathLeading(
                                                                HirTypePathLeading {
                                                                    ty_path: TypePath(`core::basic::unit`, `Extern`),
                                                                    template_arguments: [],
                                                                    always_copyable: true,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    always_copyable: false,
                                                },
                                            ),
                                            contracted_quary: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                            always_copyable: false,
                                            place_contract_site: HirPlaceContractSite {
                                                place_contracts: [],
                                            },
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            contracted_quary_after_coercion: HirContractedQuary {
                                                contract: None,
                                                quary: Transient,
                                            },
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Eval {
                                            expr: 2,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                        Eval {
                                            expr: 4,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                        Eval {
                                            expr: 6,
                                            coercion: Some(
                                                Trivial(
                                                    TrivialHirEagerCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            ),
                                            discarded: false,
                                        },
                                        Match {
                                            opd: 0,
                                            contract: Pure,
                                            case_branches: [
                                                HirEagerCaseBranch {
                                                    pattern: 0,
                                                    stmts: ArenaIdxRange(
                                                        0..1,
                                                    ),
                                                },
                                                HirEagerCaseBranch {
                                                    pattern: 1,
                                                    stmts: ArenaIdxRange(
                                                        1..2,
                                                    ),
                                                },
                                                HirEagerCaseBranch {
                                                    pattern: 2,
                                                    stmts: ArenaIdxRange(
                                                        2..3,
                                                    ),
                                                },
                                            ],
                                        },
                                    ],
                                },
                                pattern_arena: Arena {
                                    data: [
                                        HirEagerPatternEntry {
                                            data: HirEagerPatternData::UnitPath(
                                                PatternPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAllResult::ConfidentYes`),
                                                ),
                                            ),
                                            contract: Pure,
                                        },
                                        HirEagerPatternEntry {
                                            data: HirEagerPatternData::UnitPath(
                                                PatternPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAllResult::ConfidentNo`),
                                                ),
                                            ),
                                            contract: Pure,
                                        },
                                        HirEagerPatternEntry {
                                            data: HirEagerPatternData::UnitPath(
                                                PatternPath::TypeVariant(
                                                    TypeVariantPath(`malamute::OneVsAllResult::Unconfident`),
                                                ),
                                            ),
                                            contract: Pure,
                                        },
                                    ],
                                },
                                comptime_variable_region_data: HirEagerComptimeVariableRegionData {
                                    arena: Arena {
                                        data: [],
                                    },
                                },
                                runtime_variable_region_data: HirEagerRuntimeVariableRegionData {
                                    arena: Arena {
                                        data: [
                                            HirEagerRuntimeVariableEntry {
                                                name: HirEagerRuntimeVariableName::Ident(
                                                    `one_vs_all_result`,
                                                ),
                                                data: HirEagerRuntimeVariableData::ParenateParameter,
                                            },
                                        ],
                                    },
                                    self_value_variable: None,
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
]
```