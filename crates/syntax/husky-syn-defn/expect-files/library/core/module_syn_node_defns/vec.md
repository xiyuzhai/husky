Ok(
    [
        SynNodeDefn::MajorItem(
            MajorItemSynNodeDefn::Type(
                TypeSynNodeDefn::Extern(
                    ExternTypeSynNodeDefn {
                        syn_node_path: TypeSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypePath(`core::vec::Vec`, `Extern`),
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: ExternTypeSynNodeDecl {
                            syn_node_path: TypeSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypePath(`core::vec::Vec`, `Extern`),
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                Some(
                                    Generics {
                                        langle: LaOrLtRegionalToken(
                                            RegionalTokenIdx(
                                                4,
                                            ),
                                        ),
                                        template_parameters: [
                                            TemplateParameterObelisk {
                                                annotated_variance_token: Some(
                                                    VarianceRegionalToken::Covariant(
                                                        CovariantRegionalToken {
                                                            regional_token_idx: RegionalTokenIdx(
                                                                5,
                                                            ),
                                                        },
                                                    ),
                                                ),
                                                symbol: 1,
                                                variant: TemplateParameterDeclPatternVariant::Type {
                                                    ident_token: IdentRegionalToken {
                                                        ident: `E`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                    },
                                                    traits: None,
                                                },
                                            },
                                        ],
                                        commas: [],
                                        decl_list_result: Ok(
                                            (),
                                        ),
                                        rangle: RaOrGtRegionalToken(
                                            RegionalTokenIdx(
                                                7,
                                            ),
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Type(
                                                TypeSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypePath(`core::vec::Vec`, `Extern`),
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [
                                                CurrentSynSymbol {
                                                    modifier: Const,
                                                    access_start: RegionalTokenIdx(
                                                        7,
                                                    ),
                                                    access_end: None,
                                                    variant: CurrentSynSymbolVariant::TemplateParameter {
                                                        syn_attrs: TemplateParameterSynAttrs {
                                                            syn_attrs: [],
                                                        },
                                                        annotated_variance_token: Some(
                                                            VarianceRegionalToken::Covariant(
                                                                CovariantRegionalToken {
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                        ),
                                                        template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                            ident_token: IdentRegionalToken {
                                                                ident: `E`,
                                                                regional_token_idx: RegionalTokenIdx(
                                                                    6,
                                                                ),
                                                            },
                                                        },
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [
                                            (
                                                TemplateTypeParameter,
                                                ArenaIdxRange(
                                                    1..2,
                                                ),
                                            ),
                                        ],
                                    },
                                    roots: [],
                                },
                            },
                        },
                    },
                ),
            ),
        ),
        SynNodeDefn::Attr(
            AttrSynNodeDefn {
                syn_node_decl: Derive(
                    DeriveAttrSynNodeDecl(
                        Id {
                            value: 17,
                        },
                    ),
                ),
            },
        ),
        SynNodeDefn::ImplBlock(
            ImplBlockSynNodeDecl::Type(
                TypeImplBlockSynNodeDecl {
                    syn_node_path: TypeImplBlockSynNodePath {
                        path: TypeImplBlockPath {
                            module_path: `core::vec`,
                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                            disambiguator: 0,
                        },
                    },
                    impl_regional_token: ImplRegionalToken {
                        regional_token_idx: RegionalTokenIdx(
                            1,
                        ),
                    },
                    template_parameter_decl_list: Ok(
                        Some(
                            Generics {
                                langle: LaOrLtRegionalToken(
                                    RegionalTokenIdx(
                                        2,
                                    ),
                                ),
                                template_parameters: [
                                    TemplateParameterObelisk {
                                        annotated_variance_token: None,
                                        symbol: 1,
                                        variant: TemplateParameterDeclPatternVariant::Type {
                                            ident_token: IdentRegionalToken {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    3,
                                                ),
                                            },
                                            traits: None,
                                        },
                                    },
                                ],
                                commas: [],
                                decl_list_result: Ok(
                                    (),
                                ),
                                rangle: RaOrGtRegionalToken(
                                    RegionalTokenIdx(
                                        4,
                                    ),
                                ),
                            },
                        ),
                    ),
                    self_ty_expr: SelfTypeObelisk {
                        expr: 3,
                    },
                    eol_colon: Ok(
                        EolRegionalToken::Colon(
                            EolColonRegionalToken {
                                regional_token_idx: RegionalTokenIdx(
                                    7,
                                ),
                            },
                        ),
                    ),
                    syn_expr_region: SynExprRegion {
                        data: SynExprRegionData {
                            parent: None,
                            path: RegionPath::Decl(
                                ItemSynNodePath::ImplBlock(
                                    ImplBlockSynNodePath::TypeImplBlock(
                                        TypeImplBlockSynNodePath {
                                            path: TypeImplBlockPath {
                                                module_path: `core::vec`,
                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                disambiguator: 0,
                                            },
                                        },
                                    ),
                                ),
                            ),
                            expr_arena: Arena {
                                data: [
                                    SynExpr::PrincipalEntityPath {
                                        item_path_expr: 1,
                                        opt_path: Some(
                                            PrincipalEntityPath::MajorItem(
                                                MajorItemPath::Type(
                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                ),
                                            ),
                                        ),
                                    },
                                    SynExpr::CurrentSymbol {
                                        ident: `E`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                        current_symbol_idx: 1,
                                        current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                            template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                ident_token: IdentRegionalToken {
                                                    ident: `E`,
                                                    regional_token_idx: RegionalTokenIdx(
                                                        3,
                                                    ),
                                                },
                                            },
                                        },
                                    },
                                    SynExpr::ExplicitApplication {
                                        function_expr_idx: 1,
                                        argument_expr_idx: 2,
                                    },
                                ],
                            },
                            principal_item_path_expr_arena: Arena {
                                data: [
                                    PrincipalEntityPathExpr::Root {
                                        path_name_token: PathNameRegionalToken::Ident(
                                            IdentRegionalToken {
                                                ident: `Vec`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    5,
                                                ),
                                            },
                                        ),
                                        principal_entity_path: PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Type(
                                                TypePath(`core::vec::Vec`, `Extern`),
                                            ),
                                        ),
                                    },
                                ],
                            },
                            stmt_arena: Arena {
                                data: [],
                            },
                            pattern_expr_region: SynPatternExprRegion {
                                pattern_expr_arena: Arena {
                                    data: [],
                                },
                                pattern_expr_contracts: ArenaMap {
                                    data: [],
                                },
                                pattern_infos: [],
                                pattern_symbol_arena: Arena {
                                    data: [],
                                },
                                pattern_symbol_maps: [],
                                pattern_symbol_modifiers: ArenaMap {
                                    data: [],
                                },
                            },
                            symbol_region: SynSymbolRegion {
                                inherited_symbol_arena: Arena {
                                    data: [],
                                },
                                current_symbol_arena: Arena {
                                    data: [
                                        CurrentSynSymbol {
                                            modifier: Const,
                                            access_start: RegionalTokenIdx(
                                                4,
                                            ),
                                            access_end: None,
                                            variant: CurrentSynSymbolVariant::TemplateParameter {
                                                syn_attrs: TemplateParameterSynAttrs {
                                                    syn_attrs: [],
                                                },
                                                annotated_variance_token: None,
                                                template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                    ident_token: IdentRegionalToken {
                                                        ident: `E`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            3,
                                                        ),
                                                    },
                                                },
                                            },
                                        },
                                    ],
                                },
                                allow_self_type: True,
                                allow_self_value: False,
                                pattern_ty_constraints: [
                                    (
                                        TemplateTypeParameter,
                                        ArenaIdxRange(
                                            1..2,
                                        ),
                                    ),
                                ],
                            },
                            roots: [
                                SynExprRoot {
                                    kind: SelfType,
                                    expr_idx: 3,
                                },
                            ],
                        },
                    },
                },
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `ilen`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `ilen`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: None,
                                    comma_after_self_parameter: None,
                                    parenate_parameters: [],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            5,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            6,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 1,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            8,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `ilen`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::i32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `i32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::num::i32`, `Extern`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 1,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `push`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `push`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: Some(
                                        SelfParameterObelisk {
                                            ephem_symbol_modifier_token_group: Some(
                                                AmbersandMut(
                                                    AmbersandRegionalToken(
                                                        RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    ),
                                                    None,
                                                    MutRegionalToken {
                                                        regional_token_idx: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                    },
                                                ),
                                            ),
                                            self_value_token: SelfValueRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    7,
                                                ),
                                            },
                                        },
                                    ),
                                    comma_after_self_parameter: Some(
                                        CommaRegionalToken(
                                            RegionalTokenIdx(
                                                8,
                                            ),
                                        ),
                                    ),
                                    parenate_parameters: [
                                        SpecificParameterObelisk::Regular {
                                            pattern: 1,
                                            variables: ArenaIdxRange(
                                                1..2,
                                            ),
                                            colon: ColonRegionalToken(
                                                RegionalTokenIdx(
                                                    10,
                                                ),
                                            ),
                                            ty: 1,
                                        },
                                    ],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            12,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                None,
                            ),
                            return_ty: Ok(
                                None,
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            13,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `push`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [
                                                SynPatternExpr::Ident {
                                                    symbol_modifier_keyword_group: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `e`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            9,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [
                                                None,
                                            ],
                                        },
                                        pattern_infos: [
                                            Parameter,
                                        ],
                                        pattern_symbol_arena: Arena {
                                            data: [
                                                SynPatternSymbol::Atom(
                                                    1,
                                                ),
                                            ],
                                        },
                                        pattern_symbol_maps: [
                                            [
                                                (
                                                    `e`,
                                                    1,
                                                ),
                                            ],
                                        ],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [
                                                None,
                                            ],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [
                                                CurrentSynSymbol {
                                                    modifier: None,
                                                    access_start: RegionalTokenIdx(
                                                        10,
                                                    ),
                                                    access_end: None,
                                                    variant: CurrentSynSymbolVariant::ParenateRegularParameter {
                                                        ident: `e`,
                                                        pattern_symbol_idx: 1,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [
                                            (
                                                ExplicitRegularParameter {
                                                    pattern_expr_idx: 1,
                                                    ty_expr_idx: 1,
                                                },
                                                ArenaIdxRange(
                                                    1..2,
                                                ),
                                            ),
                                        ],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ExplicitParameterType,
                                            expr_idx: 1,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `first`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `first`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: None,
                                    comma_after_self_parameter: None,
                                    parenate_parameters: [],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            5,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            6,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 3,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            9,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `first`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::option::Option`, `Enum`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    8,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::ExplicitApplication {
                                                function_expr_idx: 1,
                                                argument_expr_idx: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `Option`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::option::Option`, `Enum`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 3,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `last`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `last`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: None,
                                    comma_after_self_parameter: None,
                                    parenate_parameters: [],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            5,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            6,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 3,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            9,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `last`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::option::Option`, `Enum`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    8,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::ExplicitApplication {
                                                function_expr_idx: 1,
                                                argument_expr_idx: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `Option`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::option::Option`, `Enum`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 3,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `pop`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `pop`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: Some(
                                        SelfParameterObelisk {
                                            ephem_symbol_modifier_token_group: Some(
                                                AmbersandMut(
                                                    AmbersandRegionalToken(
                                                        RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    ),
                                                    None,
                                                    MutRegionalToken {
                                                        regional_token_idx: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                    },
                                                ),
                                            ),
                                            self_value_token: SelfValueRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    7,
                                                ),
                                            },
                                        },
                                    ),
                                    comma_after_self_parameter: None,
                                    parenate_parameters: [],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            8,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            9,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 3,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `pop`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::option::Option`, `Enum`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::ExplicitApplication {
                                                function_expr_idx: 1,
                                                argument_expr_idx: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `Option`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            10,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::option::Option`, `Enum`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 3,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `collect_leashes`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `collect_leashes`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: Some(
                                        SelfParameterObelisk {
                                            ephem_symbol_modifier_token_group: Some(
                                                Tilde(
                                                    TildeRegionalToken(
                                                        RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    ),
                                                ),
                                            ),
                                            self_value_token: SelfValueRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                            },
                                        },
                                    ),
                                    comma_after_self_parameter: None,
                                    parenate_parameters: [],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            7,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            8,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 4,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            13,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `collect_leashes`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    12,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::List {
                                                lbox_regional_token_idx: RegionalTokenIdx(
                                                    9,
                                                ),
                                                items: [],
                                                rbox_regional_token_idx: RegionalTokenIdx(
                                                    10,
                                                ),
                                            },
                                            SynExpr::Prefix {
                                                opr: Tilde,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                                opd: 1,
                                            },
                                            SynExpr::ExplicitApplication {
                                                function_expr_idx: 2,
                                                argument_expr_idx: 3,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [],
                                        },
                                        pattern_infos: [],
                                        pattern_symbol_arena: Arena {
                                            data: [],
                                        },
                                        pattern_symbol_maps: [],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 4,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `cyclic_slice_leashed`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `cyclic_slice_leashed`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: Some(
                                        SelfParameterObelisk {
                                            ephem_symbol_modifier_token_group: Some(
                                                Tilde(
                                                    TildeRegionalToken(
                                                        RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    ),
                                                ),
                                            ),
                                            self_value_token: SelfValueRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                            },
                                        },
                                    ),
                                    comma_after_self_parameter: Some(
                                        CommaRegionalToken(
                                            RegionalTokenIdx(
                                                7,
                                            ),
                                        ),
                                    ),
                                    parenate_parameters: [
                                        SpecificParameterObelisk::Regular {
                                            pattern: 1,
                                            variables: ArenaIdxRange(
                                                1..2,
                                            ),
                                            colon: ColonRegionalToken(
                                                RegionalTokenIdx(
                                                    9,
                                                ),
                                            ),
                                            ty: 1,
                                        },
                                        SpecificParameterObelisk::Regular {
                                            pattern: 2,
                                            variables: ArenaIdxRange(
                                                2..3,
                                            ),
                                            colon: ColonRegionalToken(
                                                RegionalTokenIdx(
                                                    13,
                                                ),
                                            ),
                                            ty: 2,
                                        },
                                    ],
                                    commas: [
                                        CommaRegionalToken(
                                            RegionalTokenIdx(
                                                11,
                                            ),
                                        ),
                                    ],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            15,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            16,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 6,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            20,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `cyclic_slice_leashed`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::i32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 2,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::i32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 3,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::slice::CyclicSlice`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::Prefix {
                                                opr: Tilde,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    17,
                                                ),
                                                opd: 3,
                                            },
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    19,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::ExplicitApplication {
                                                function_expr_idx: 4,
                                                argument_expr_idx: 5,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `i32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            10,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::num::i32`, `Extern`),
                                                    ),
                                                ),
                                            },
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `i32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            14,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::num::i32`, `Extern`),
                                                    ),
                                                ),
                                            },
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `CyclicSlice`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            18,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::slice::CyclicSlice`, `Extern`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [
                                                SynPatternExpr::Ident {
                                                    symbol_modifier_keyword_group: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `start`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            8,
                                                        ),
                                                    },
                                                },
                                                SynPatternExpr::Ident {
                                                    symbol_modifier_keyword_group: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `end`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            12,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [
                                                None,
                                                None,
                                            ],
                                        },
                                        pattern_infos: [
                                            Parameter,
                                            Parameter,
                                        ],
                                        pattern_symbol_arena: Arena {
                                            data: [
                                                SynPatternSymbol::Atom(
                                                    1,
                                                ),
                                                SynPatternSymbol::Atom(
                                                    2,
                                                ),
                                            ],
                                        },
                                        pattern_symbol_maps: [
                                            [
                                                (
                                                    `start`,
                                                    1,
                                                ),
                                            ],
                                            [
                                                (
                                                    `end`,
                                                    2,
                                                ),
                                            ],
                                        ],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [
                                                None,
                                                None,
                                            ],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [
                                                CurrentSynSymbol {
                                                    modifier: None,
                                                    access_start: RegionalTokenIdx(
                                                        9,
                                                    ),
                                                    access_end: None,
                                                    variant: CurrentSynSymbolVariant::ParenateRegularParameter {
                                                        ident: `start`,
                                                        pattern_symbol_idx: 1,
                                                    },
                                                },
                                                CurrentSynSymbol {
                                                    modifier: None,
                                                    access_start: RegionalTokenIdx(
                                                        13,
                                                    ),
                                                    access_end: None,
                                                    variant: CurrentSynSymbolVariant::ParenateRegularParameter {
                                                        ident: `end`,
                                                        pattern_symbol_idx: 2,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [
                                            (
                                                ExplicitRegularParameter {
                                                    pattern_expr_idx: 1,
                                                    ty_expr_idx: 1,
                                                },
                                                ArenaIdxRange(
                                                    1..2,
                                                ),
                                            ),
                                            (
                                                ExplicitRegularParameter {
                                                    pattern_expr_idx: 2,
                                                    ty_expr_idx: 2,
                                                },
                                                ArenaIdxRange(
                                                    2..3,
                                                ),
                                            ),
                                        ],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ExplicitParameterType,
                                            expr_idx: 1,
                                        },
                                        SynExprRoot {
                                            kind: ExplicitParameterType,
                                            expr_idx: 2,
                                        },
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 6,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
        SynNodeDefn::AssociatedItem(
            AssociatedItemSynNodeDefn::TypeItem(
                TypeItemSynNodeDefn::MethodFn(
                    TypeMethodFnSynNodeDefn {
                        syn_node_path: TypeItemSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: TypeItemPath {
                                    impl_block: TypeImplBlockPath {
                                        module_path: `core::vec`,
                                        ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                        disambiguator: 0,
                                    },
                                    ident: `pop_with_largest_opt_f32`,
                                    item_kind: MethodFn,
                                },
                                disambiguator: 0,
                            },
                        },
                        syn_node_decl: TypeMethodFnSynNodeDecl {
                            syn_node_path: TypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TypeItemPath {
                                        impl_block: TypeImplBlockPath {
                                            module_path: `core::vec`,
                                            ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                            disambiguator: 0,
                                        },
                                        ident: `pop_with_largest_opt_f32`,
                                        item_kind: MethodFn,
                                    },
                                    disambiguator: 0,
                                },
                            },
                            template_parameter_decl_list: Ok(
                                None,
                            ),
                            ritchie_parameter_decl_list: Ok(
                                RitchieParameters {
                                    lpar: LparRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    self_value_parameter: Some(
                                        SelfParameterObelisk {
                                            ephem_symbol_modifier_token_group: Some(
                                                AmbersandMut(
                                                    AmbersandRegionalToken(
                                                        RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    ),
                                                    None,
                                                    MutRegionalToken {
                                                        regional_token_idx: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                    },
                                                ),
                                            ),
                                            self_value_token: SelfValueRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    7,
                                                ),
                                            },
                                        },
                                    ),
                                    comma_after_self_parameter: Some(
                                        CommaRegionalToken(
                                            RegionalTokenIdx(
                                                8,
                                            ),
                                        ),
                                    ),
                                    parenate_parameters: [
                                        SpecificParameterObelisk::Regular {
                                            pattern: 1,
                                            variables: ArenaIdxRange(
                                                1..2,
                                            ),
                                            colon: ColonRegionalToken(
                                                RegionalTokenIdx(
                                                    10,
                                                ),
                                            ),
                                            ty: 4,
                                        },
                                    ],
                                    commas: [],
                                    rpar: RparRegionalToken(
                                        RegionalTokenIdx(
                                            18,
                                        ),
                                    ),
                                },
                            ),
                            light_arrow_token: Ok(
                                Some(
                                    LightArrowRegionalToken(
                                        RegionalTokenIdx(
                                            19,
                                        ),
                                    ),
                                ),
                            ),
                            return_ty: Ok(
                                Some(
                                    ReturnTypeBeforeColonObelisk {
                                        expr: 6,
                                    },
                                ),
                            ),
                            eol_colon: Ok(
                                EolRegionalToken::Semicolon(
                                    EolSemicolonRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            22,
                                        ),
                                    },
                                ),
                            ),
                            syn_expr_region: SynExprRegion {
                                data: SynExprRegionData {
                                    parent: Some(
                                        SynExprRegion {
                                            data: SynExprRegionData {
                                                parent: None,
                                                path: RegionPath::Decl(
                                                    ItemSynNodePath::ImplBlock(
                                                        ImplBlockSynNodePath::TypeImplBlock(
                                                            TypeImplBlockSynNodePath {
                                                                path: TypeImplBlockPath {
                                                                    module_path: `core::vec`,
                                                                    ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                expr_arena: Arena {
                                                    data: [
                                                        SynExpr::PrincipalEntityPath {
                                                            item_path_expr: 1,
                                                            opt_path: Some(
                                                                PrincipalEntityPath::MajorItem(
                                                                    MajorItemPath::Type(
                                                                        TypePath(`core::vec::Vec`, `Extern`),
                                                                    ),
                                                                ),
                                                            ),
                                                        },
                                                        SynExpr::CurrentSymbol {
                                                            ident: `E`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                6,
                                                            ),
                                                            current_symbol_idx: 1,
                                                            current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {
                                                                template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                                    ident_token: IdentRegionalToken {
                                                                        ident: `E`,
                                                                        regional_token_idx: RegionalTokenIdx(
                                                                            3,
                                                                        ),
                                                                    },
                                                                },
                                                            },
                                                        },
                                                        SynExpr::ExplicitApplication {
                                                            function_expr_idx: 1,
                                                            argument_expr_idx: 2,
                                                        },
                                                    ],
                                                },
                                                principal_item_path_expr_arena: Arena {
                                                    data: [
                                                        PrincipalEntityPathExpr::Root {
                                                            path_name_token: PathNameRegionalToken::Ident(
                                                                IdentRegionalToken {
                                                                    ident: `Vec`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            ),
                                                            principal_entity_path: PrincipalEntityPath::MajorItem(
                                                                MajorItemPath::Type(
                                                                    TypePath(`core::vec::Vec`, `Extern`),
                                                                ),
                                                            ),
                                                        },
                                                    ],
                                                },
                                                stmt_arena: Arena {
                                                    data: [],
                                                },
                                                pattern_expr_region: SynPatternExprRegion {
                                                    pattern_expr_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_expr_contracts: ArenaMap {
                                                        data: [],
                                                    },
                                                    pattern_infos: [],
                                                    pattern_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    pattern_symbol_maps: [],
                                                    pattern_symbol_modifiers: ArenaMap {
                                                        data: [],
                                                    },
                                                },
                                                symbol_region: SynSymbolRegion {
                                                    inherited_symbol_arena: Arena {
                                                        data: [],
                                                    },
                                                    current_symbol_arena: Arena {
                                                        data: [
                                                            CurrentSynSymbol {
                                                                modifier: Const,
                                                                access_start: RegionalTokenIdx(
                                                                    4,
                                                                ),
                                                                access_end: None,
                                                                variant: CurrentSynSymbolVariant::TemplateParameter {
                                                                    syn_attrs: TemplateParameterSynAttrs {
                                                                        syn_attrs: [],
                                                                    },
                                                                    annotated_variance_token: None,
                                                                    template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                        ident_token: IdentRegionalToken {
                                                                            ident: `E`,
                                                                            regional_token_idx: RegionalTokenIdx(
                                                                                3,
                                                                            ),
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        ],
                                                    },
                                                    allow_self_type: True,
                                                    allow_self_value: False,
                                                    pattern_ty_constraints: [
                                                        (
                                                            TemplateTypeParameter,
                                                            ArenaIdxRange(
                                                                1..2,
                                                            ),
                                                        ),
                                                    ],
                                                },
                                                roots: [
                                                    SynExprRoot {
                                                        kind: SelfType,
                                                        expr_idx: 3,
                                                    },
                                                ],
                                            },
                                        },
                                    ),
                                    path: RegionPath::Decl(
                                        ItemSynNodePath::AssociatedItem(
                                            AssociatedItemSynNodePath::TypeItem(
                                                TypeItemSynNodePath {
                                                    maybe_ambiguous_path: MaybeAmbiguousPath {
                                                        path: TypeItemPath {
                                                            impl_block: TypeImplBlockPath {
                                                                module_path: `core::vec`,
                                                                ty_path: TypePath(`core::vec::Vec`, `Extern`),
                                                                disambiguator: 0,
                                                            },
                                                            ident: `pop_with_largest_opt_f32`,
                                                            item_kind: MethodFn,
                                                        },
                                                        disambiguator: 0,
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    13,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::PrincipalEntityPath {
                                                item_path_expr: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::f32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExpr::Prefix {
                                                opr: Option,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    16,
                                                ),
                                                opd: 2,
                                            },
                                            SynExpr::Ritchie {
                                                ritchie_kind_regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                                ritchie_kind: FnType,
                                                lpar_token: LparRegionalToken(
                                                    RegionalTokenIdx(
                                                        12,
                                                    ),
                                                ),
                                                parameter_ty_items: [
                                                    SynCommaListItem {
                                                        expr_idx: 1,
                                                        comma_regional_token_idx: None,
                                                    },
                                                ],
                                                rpar_regional_token_idx: RegionalTokenIdx(
                                                    14,
                                                ),
                                                light_arrow_token: Some(
                                                    LightArrowRegionalToken(
                                                        RegionalTokenIdx(
                                                            15,
                                                        ),
                                                    ),
                                                ),
                                                return_ty_expr: Some(
                                                    3,
                                                ),
                                            },
                                            SynExpr::InheritedSymbol {
                                                ident: `E`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    21,
                                                ),
                                                inherited_symbol_idx: 1,
                                                inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(
                                                    InheritedTemplateParameterSynSymbol::Type {
                                                        ident: `E`,
                                                    },
                                                ),
                                            },
                                            SynExpr::Prefix {
                                                opr: Option,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    20,
                                                ),
                                                opd: 5,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            PrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `f32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            17,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::num::f32`, `Extern`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_expr_region: SynPatternExprRegion {
                                        pattern_expr_arena: Arena {
                                            data: [
                                                SynPatternExpr::Ident {
                                                    symbol_modifier_keyword_group: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `f`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            9,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_expr_contracts: ArenaMap {
                                            data: [
                                                None,
                                            ],
                                        },
                                        pattern_infos: [
                                            Parameter,
                                        ],
                                        pattern_symbol_arena: Arena {
                                            data: [
                                                SynPatternSymbol::Atom(
                                                    1,
                                                ),
                                            ],
                                        },
                                        pattern_symbol_maps: [
                                            [
                                                (
                                                    `f`,
                                                    1,
                                                ),
                                            ],
                                        ],
                                        pattern_symbol_modifiers: ArenaMap {
                                            data: [
                                                None,
                                            ],
                                        },
                                    },
                                    symbol_region: SynSymbolRegion {
                                        inherited_symbol_arena: Arena {
                                            data: [
                                                InheritedSynSymbol {
                                                    parent_symbol_idx: Current(
                                                        1,
                                                    ),
                                                    modifier: Const,
                                                    kind: InheritedSynSymbolKind::TemplateParameter(
                                                        InheritedTemplateParameterSynSymbol::Type {
                                                            ident: `E`,
                                                        },
                                                    ),
                                                },
                                            ],
                                        },
                                        current_symbol_arena: Arena {
                                            data: [
                                                CurrentSynSymbol {
                                                    modifier: None,
                                                    access_start: RegionalTokenIdx(
                                                        10,
                                                    ),
                                                    access_end: None,
                                                    variant: CurrentSynSymbolVariant::ParenateRegularParameter {
                                                        ident: `f`,
                                                        pattern_symbol_idx: 1,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: True,
                                        allow_self_value: True,
                                        pattern_ty_constraints: [
                                            (
                                                ExplicitRegularParameter {
                                                    pattern_expr_idx: 1,
                                                    ty_expr_idx: 4,
                                                },
                                                ArenaIdxRange(
                                                    1..2,
                                                ),
                                            ),
                                        ],
                                    },
                                    roots: [
                                        SynExprRoot {
                                            kind: ExplicitParameterType,
                                            expr_idx: 4,
                                        },
                                        SynExprRoot {
                                            kind: ReturnType,
                                            expr_idx: 6,
                                        },
                                    ],
                                },
                            },
                        },
                        body_with_syn_expr_region: None,
                    },
                ),
            ),
        ),
    ],
)