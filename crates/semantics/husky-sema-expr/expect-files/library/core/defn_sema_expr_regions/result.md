[
    SemaExprRegion {
        [salsa id]: 2,
        path: RegionPath::Defn(
            ItemSynNodePath::AssociatedItem(
                AssociatedItemSynNodePath::TraitForTypeItem(
                    TraitForTypeItemSynNodePath {
                        maybe_ambiguous_path: MaybeAmbiguousPath {
                            path: TraitForTypeItemPath {
                                impl_block: TraitForTypeImplBlockPath {
                                    module_path: `core::result`,
                                    trai_path: TraitPath(`core::ops::Unveil`),
                                    ty_sketch: TypeSketch::Path(
                                        TypePath(`core::result::Result`, `Enum`),
                                    ),
                                    disambiguator: 0,
                                },
                                ident: `branch`,
                                item_kind: MethodFn,
                            },
                            disambiguator: 0,
                        },
                    },
                ),
            ),
        ),
        syn_expr_region: SynExprRegion {
            data: SynExprRegionData {
                parent: Some(
                    SynExprRegion {
                        data: SynExprRegionData {
                            parent: Some(
                                SynExprRegion {
                                    data: SynExprRegionData {
                                        parent: None,
                                        path: RegionPath::Decl(
                                            ItemSynNodePath::ImplBlock(
                                                ImplBlockSynNodePath::TraitForTypeImplBlock(
                                                    TraitForTypeImplBlockSynNodePath {
                                                        path: TraitForTypeImplBlockPath {
                                                            module_path: `core::result`,
                                                            trai_path: TraitPath(`core::ops::Unveil`),
                                                            ty_sketch: TypeSketch::Path(
                                                                TypePath(`core::result::Result`, `Enum`),
                                                            ),
                                                            disambiguator: 0,
                                                        },
                                                    },
                                                ),
                                            ),
                                        ),
                                        expr_arena: Arena {
                                            data: [
                                                SynExprData::PrincipalEntityPath {
                                                    path_expr_idx: 3,
                                                    opt_path: Some(
                                                        PrincipalEntityPath::MajorItem(
                                                            MajorItemPath::Trait(
                                                                TraitPath(`core::ops::Unveil`),
                                                            ),
                                                        ),
                                                    ),
                                                },
                                                SynExprData::PrincipalEntityPath {
                                                    path_expr_idx: 4,
                                                    opt_path: Some(
                                                        PrincipalEntityPath::MajorItem(
                                                            MajorItemPath::Type(
                                                                TypePath(`core::result::Result`, `Enum`),
                                                            ),
                                                        ),
                                                    ),
                                                },
                                                SynExprData::ExplicitApplication {
                                                    function_expr_idx: 1,
                                                    argument_expr_idx: 2,
                                                },
                                                SynExprData::CurrentSymbol {
                                                    ident: `T2`,
                                                    regional_token_idx: RegionalTokenIdx(
                                                        17,
                                                    ),
                                                    current_symbol_idx: 2,
                                                    current_symbol_kind: SynCurrentSymbolKind::ImplicitParameter {
                                                        template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                            ident_token: IdentRegionalToken {
                                                                ident: `T2`,
                                                                regional_token_idx: RegionalTokenIdx(
                                                                    5,
                                                                ),
                                                            },
                                                        },
                                                    },
                                                },
                                                SynExprData::ExplicitApplication {
                                                    function_expr_idx: 3,
                                                    argument_expr_idx: 4,
                                                },
                                                SynExprData::CurrentSymbol {
                                                    ident: `E2`,
                                                    regional_token_idx: RegionalTokenIdx(
                                                        18,
                                                    ),
                                                    current_symbol_idx: 4,
                                                    current_symbol_kind: SynCurrentSymbolKind::ImplicitParameter {
                                                        template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                            ident_token: IdentRegionalToken {
                                                                ident: `E2`,
                                                                regional_token_idx: RegionalTokenIdx(
                                                                    9,
                                                                ),
                                                            },
                                                        },
                                                    },
                                                },
                                                SynExprData::ExplicitApplication {
                                                    function_expr_idx: 5,
                                                    argument_expr_idx: 6,
                                                },
                                                SynExprData::PrincipalEntityPath {
                                                    path_expr_idx: 5,
                                                    opt_path: Some(
                                                        PrincipalEntityPath::MajorItem(
                                                            MajorItemPath::Type(
                                                                TypePath(`core::result::Result`, `Enum`),
                                                            ),
                                                        ),
                                                    ),
                                                },
                                                SynExprData::CurrentSymbol {
                                                    ident: `T1`,
                                                    regional_token_idx: RegionalTokenIdx(
                                                        21,
                                                    ),
                                                    current_symbol_idx: 1,
                                                    current_symbol_kind: SynCurrentSymbolKind::ImplicitParameter {
                                                        template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                            ident_token: IdentRegionalToken {
                                                                ident: `T1`,
                                                                regional_token_idx: RegionalTokenIdx(
                                                                    3,
                                                                ),
                                                            },
                                                        },
                                                    },
                                                },
                                                SynExprData::ExplicitApplication {
                                                    function_expr_idx: 8,
                                                    argument_expr_idx: 9,
                                                },
                                                SynExprData::CurrentSymbol {
                                                    ident: `E1`,
                                                    regional_token_idx: RegionalTokenIdx(
                                                        22,
                                                    ),
                                                    current_symbol_idx: 3,
                                                    current_symbol_kind: SynCurrentSymbolKind::ImplicitParameter {
                                                        template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {
                                                            ident_token: IdentRegionalToken {
                                                                ident: `E1`,
                                                                regional_token_idx: RegionalTokenIdx(
                                                                    7,
                                                                ),
                                                            },
                                                        },
                                                    },
                                                },
                                                SynExprData::ExplicitApplication {
                                                    function_expr_idx: 10,
                                                    argument_expr_idx: 11,
                                                },
                                            ],
                                        },
                                        principal_item_path_expr_arena: Arena {
                                            data: [
                                                SynPrincipalEntityPathExpr::Root {
                                                    path_name_token: PathNameRegionalToken::CrateRoot(
                                                        CrateRegionalToken {
                                                            token_idx: RegionalTokenIdx(
                                                                11,
                                                            ),
                                                        },
                                                    ),
                                                    principal_entity_path: PrincipalEntityPath::Module(
                                                        `core`,
                                                    ),
                                                },
                                                SynPrincipalEntityPathExpr::Subitem {
                                                    parent: 1,
                                                    colon_colon_token: ColonColonRegionalToken(
                                                        RegionalTokenIdx(
                                                            12,
                                                        ),
                                                    ),
                                                    ident_token: Ok(
                                                        IdentRegionalToken {
                                                            ident: `ops`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                13,
                                                            ),
                                                        },
                                                    ),
                                                    path: Ok(
                                                        PrincipalEntityPath::Module(
                                                            `core::ops`,
                                                        ),
                                                    ),
                                                },
                                                SynPrincipalEntityPathExpr::Subitem {
                                                    parent: 2,
                                                    colon_colon_token: ColonColonRegionalToken(
                                                        RegionalTokenIdx(
                                                            14,
                                                        ),
                                                    ),
                                                    ident_token: Ok(
                                                        IdentRegionalToken {
                                                            ident: `Unveil`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                15,
                                                            ),
                                                        },
                                                    ),
                                                    path: Ok(
                                                        PrincipalEntityPath::MajorItem(
                                                            MajorItemPath::Trait(
                                                                TraitPath(`core::ops::Unveil`),
                                                            ),
                                                        ),
                                                    ),
                                                },
                                                SynPrincipalEntityPathExpr::Root {
                                                    path_name_token: PathNameRegionalToken::Ident(
                                                        IdentRegionalToken {
                                                            ident: `Result`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                16,
                                                            ),
                                                        },
                                                    ),
                                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::result::Result`, `Enum`),
                                                        ),
                                                    ),
                                                },
                                                SynPrincipalEntityPathExpr::Root {
                                                    path_name_token: PathNameRegionalToken::Ident(
                                                        IdentRegionalToken {
                                                            ident: `Result`,
                                                            regional_token_idx: RegionalTokenIdx(
                                                                20,
                                                            ),
                                                        },
                                                    ),
                                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::result::Result`, `Enum`),
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
                                                    SynCurrentSymbol {
                                                        modifier: Const,
                                                        access_start: RegionalTokenIdx(
                                                            4,
                                                        ),
                                                        access_end: None,
                                                        variant: SynCurrentSymbolVariant::TemplateParameter {
                                                            syn_attrs: TemplateParameterSynAttrs {
                                                                syn_attrs: [],
                                                            },
                                                            annotated_variance_token: None,
                                                            template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                ident_token: IdentRegionalToken {
                                                                    ident: `T1`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        3,
                                                                    ),
                                                                },
                                                            },
                                                        },
                                                    },
                                                    SynCurrentSymbol {
                                                        modifier: Const,
                                                        access_start: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                        access_end: None,
                                                        variant: SynCurrentSymbolVariant::TemplateParameter {
                                                            syn_attrs: TemplateParameterSynAttrs {
                                                                syn_attrs: [],
                                                            },
                                                            annotated_variance_token: None,
                                                            template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                ident_token: IdentRegionalToken {
                                                                    ident: `T2`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        5,
                                                                    ),
                                                                },
                                                            },
                                                        },
                                                    },
                                                    SynCurrentSymbol {
                                                        modifier: Const,
                                                        access_start: RegionalTokenIdx(
                                                            8,
                                                        ),
                                                        access_end: None,
                                                        variant: SynCurrentSymbolVariant::TemplateParameter {
                                                            syn_attrs: TemplateParameterSynAttrs {
                                                                syn_attrs: [],
                                                            },
                                                            annotated_variance_token: None,
                                                            template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                ident_token: IdentRegionalToken {
                                                                    ident: `E1`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        7,
                                                                    ),
                                                                },
                                                            },
                                                        },
                                                    },
                                                    SynCurrentSymbol {
                                                        modifier: Const,
                                                        access_start: RegionalTokenIdx(
                                                            10,
                                                        ),
                                                        access_end: None,
                                                        variant: SynCurrentSymbolVariant::TemplateParameter {
                                                            syn_attrs: TemplateParameterSynAttrs {
                                                                syn_attrs: [],
                                                            },
                                                            annotated_variance_token: None,
                                                            template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {
                                                                ident_token: IdentRegionalToken {
                                                                    ident: `E2`,
                                                                    regional_token_idx: RegionalTokenIdx(
                                                                        9,
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
                                                (
                                                    TemplateTypeParameter,
                                                    ArenaIdxRange(
                                                        2..3,
                                                    ),
                                                ),
                                                (
                                                    TemplateTypeParameter,
                                                    ArenaIdxRange(
                                                        3..4,
                                                    ),
                                                ),
                                                (
                                                    TemplateTypeParameter,
                                                    ArenaIdxRange(
                                                        4..5,
                                                    ),
                                                ),
                                            ],
                                        },
                                        roots: [
                                            SynExprRoot {
                                                kind: Trait,
                                                syn_expr_idx: 7,
                                            },
                                            SynExprRoot {
                                                kind: SelfType,
                                                syn_expr_idx: 12,
                                            },
                                        ],
                                        has_self_lifetime: false,
                                        has_self_place: false,
                                    },
                                },
                            ),
                            path: RegionPath::Decl(
                                ItemSynNodePath::AssociatedItem(
                                    AssociatedItemSynNodePath::TraitForTypeItem(
                                        TraitForTypeItemSynNodePath {
                                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                                path: TraitForTypeItemPath {
                                                    impl_block: TraitForTypeImplBlockPath {
                                                        module_path: `core::result`,
                                                        trai_path: TraitPath(`core::ops::Unveil`),
                                                        ty_sketch: TypeSketch::Path(
                                                            TypePath(`core::result::Result`, `Enum`),
                                                        ),
                                                        disambiguator: 0,
                                                    },
                                                    ident: `branch`,
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
                                    SynExprData::PrincipalEntityPath {
                                        path_expr_idx: 2,
                                        opt_path: Some(
                                            PrincipalEntityPath::MajorItem(
                                                MajorItemPath::Type(
                                                    TypePath(`core::result::Result`, `Enum`),
                                                ),
                                            ),
                                        ),
                                    },
                                    SynExprData::InheritedSymbol {
                                        ident: `T2`,
                                        regional_token_idx: RegionalTokenIdx(
                                            7,
                                        ),
                                        inherited_symbol_idx: 2,
                                        inherited_symbol_kind: SynInheritedSymbolKind::TemplateParameter(
                                            InheritedTemplateParameterSynSymbol::Type {
                                                ident: `T2`,
                                            },
                                        ),
                                    },
                                    SynExprData::ExplicitApplication {
                                        function_expr_idx: 1,
                                        argument_expr_idx: 2,
                                    },
                                    SynExprData::InheritedSymbol {
                                        ident: `E2`,
                                        regional_token_idx: RegionalTokenIdx(
                                            8,
                                        ),
                                        inherited_symbol_idx: 4,
                                        inherited_symbol_kind: SynInheritedSymbolKind::TemplateParameter(
                                            InheritedTemplateParameterSynSymbol::Type {
                                                ident: `E2`,
                                            },
                                        ),
                                    },
                                    SynExprData::ExplicitApplication {
                                        function_expr_idx: 3,
                                        argument_expr_idx: 4,
                                    },
                                    SynExprData::PrincipalEntityPath {
                                        path_expr_idx: 3,
                                        opt_path: Some(
                                            PrincipalEntityPath::MajorItem(
                                                MajorItemPath::Type(
                                                    TypePath(`core::result::Result`, `Enum`),
                                                ),
                                            ),
                                        ),
                                    },
                                    SynExprData::InheritedSymbol {
                                        ident: `T1`,
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                        inherited_symbol_idx: 1,
                                        inherited_symbol_kind: SynInheritedSymbolKind::TemplateParameter(
                                            InheritedTemplateParameterSynSymbol::Type {
                                                ident: `T1`,
                                            },
                                        ),
                                    },
                                    SynExprData::ExplicitApplication {
                                        function_expr_idx: 6,
                                        argument_expr_idx: 7,
                                    },
                                    SynExprData::InheritedSymbol {
                                        ident: `E1`,
                                        regional_token_idx: RegionalTokenIdx(
                                            13,
                                        ),
                                        inherited_symbol_idx: 3,
                                        inherited_symbol_kind: SynInheritedSymbolKind::TemplateParameter(
                                            InheritedTemplateParameterSynSymbol::Type {
                                                ident: `E1`,
                                            },
                                        ),
                                    },
                                    SynExprData::ExplicitApplication {
                                        function_expr_idx: 8,
                                        argument_expr_idx: 9,
                                    },
                                ],
                            },
                            principal_item_path_expr_arena: Arena {
                                data: [
                                    SynPrincipalEntityPathExpr::Root {
                                        path_name_token: PathNameRegionalToken::Ident(
                                            IdentRegionalToken {
                                                ident: `result`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    4,
                                                ),
                                            },
                                        ),
                                        principal_entity_path: PrincipalEntityPath::Module(
                                            `core::result`,
                                        ),
                                    },
                                    SynPrincipalEntityPathExpr::Root {
                                        path_name_token: PathNameRegionalToken::Ident(
                                            IdentRegionalToken {
                                                ident: `Result`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                            },
                                        ),
                                        principal_entity_path: PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Type(
                                                TypePath(`core::result::Result`, `Enum`),
                                            ),
                                        ),
                                    },
                                    SynPrincipalEntityPathExpr::Root {
                                        path_name_token: PathNameRegionalToken::Ident(
                                            IdentRegionalToken {
                                                ident: `Result`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                            },
                                        ),
                                        principal_entity_path: PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Type(
                                                TypePath(`core::result::Result`, `Enum`),
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
                                            symbol_modifier_tokens: None,
                                            ident_token: IdentRegionalToken {
                                                ident: `result`,
                                                regional_token_idx: RegionalTokenIdx(
                                                    4,
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
                                            `result`,
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
                                        SynInheritedSymbol {
                                            parent_symbol_idx: Current(
                                                1,
                                            ),
                                            modifier: Const,
                                            kind: SynInheritedSymbolKind::TemplateParameter(
                                                InheritedTemplateParameterSynSymbol::Type {
                                                    ident: `T1`,
                                                },
                                            ),
                                        },
                                        SynInheritedSymbol {
                                            parent_symbol_idx: Current(
                                                2,
                                            ),
                                            modifier: Const,
                                            kind: SynInheritedSymbolKind::TemplateParameter(
                                                InheritedTemplateParameterSynSymbol::Type {
                                                    ident: `T2`,
                                                },
                                            ),
                                        },
                                        SynInheritedSymbol {
                                            parent_symbol_idx: Current(
                                                3,
                                            ),
                                            modifier: Const,
                                            kind: SynInheritedSymbolKind::TemplateParameter(
                                                InheritedTemplateParameterSynSymbol::Type {
                                                    ident: `E1`,
                                                },
                                            ),
                                        },
                                        SynInheritedSymbol {
                                            parent_symbol_idx: Current(
                                                4,
                                            ),
                                            modifier: Const,
                                            kind: SynInheritedSymbolKind::TemplateParameter(
                                                InheritedTemplateParameterSynSymbol::Type {
                                                    ident: `E2`,
                                                },
                                            ),
                                        },
                                    ],
                                },
                                current_symbol_arena: Arena {
                                    data: [
                                        SynCurrentSymbol {
                                            modifier: None,
                                            access_start: RegionalTokenIdx(
                                                5,
                                            ),
                                            access_end: None,
                                            variant: SynCurrentSymbolVariant::ParenateRegularParameter {
                                                ident: `result`,
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
                                            syn_pattern_root: SynPatternRoot(
                                                1,
                                            ),
                                            ty_expr_idx: 5,
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
                                    syn_expr_idx: 5,
                                },
                                SynExprRoot {
                                    kind: ReturnType,
                                    syn_expr_idx: 10,
                                },
                            ],
                            has_self_lifetime: false,
                            has_self_place: false,
                        },
                    },
                ),
                path: RegionPath::Defn(
                    ItemSynNodePath::AssociatedItem(
                        AssociatedItemSynNodePath::TraitForTypeItem(
                            TraitForTypeItemSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: TraitForTypeItemPath {
                                        impl_block: TraitForTypeImplBlockPath {
                                            module_path: `core::result`,
                                            trai_path: TraitPath(`core::ops::Unveil`),
                                            ty_sketch: TypeSketch::Path(
                                                TypePath(`core::result::Result`, `Enum`),
                                            ),
                                            disambiguator: 0,
                                        },
                                        ident: `branch`,
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
                        SynExprData::Todo {
                            regional_token_idx: RegionalTokenIdx(
                                1,
                            ),
                        },
                        SynExprData::Block {
                            stmts: ArenaIdxRange(
                                1..2,
                            ),
                        },
                    ],
                },
                principal_item_path_expr_arena: Arena {
                    data: [],
                },
                stmt_arena: Arena {
                    data: [
                        SynStmtData::Eval {
                            expr_idx: 1,
                            eol_semicolon: Ok(
                                None,
                            ),
                        },
                    ],
                },
                pattern_expr_region: SynPatternExprRegion {
                    pattern_expr_arena: Arena {
                        data: [],
                    },
                    pattern_expr_contracts: ArenaMap {
                        data: [],
                    },
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
                            SynInheritedSymbol {
                                parent_symbol_idx: Current(
                                    1,
                                ),
                                modifier: Const,
                                kind: SynInheritedSymbolKind::TemplateParameter(
                                    InheritedTemplateParameterSynSymbol::Type {
                                        ident: `T1`,
                                    },
                                ),
                            },
                            SynInheritedSymbol {
                                parent_symbol_idx: Current(
                                    2,
                                ),
                                modifier: Const,
                                kind: SynInheritedSymbolKind::TemplateParameter(
                                    InheritedTemplateParameterSynSymbol::Type {
                                        ident: `T2`,
                                    },
                                ),
                            },
                            SynInheritedSymbol {
                                parent_symbol_idx: Current(
                                    3,
                                ),
                                modifier: Const,
                                kind: SynInheritedSymbolKind::TemplateParameter(
                                    InheritedTemplateParameterSynSymbol::Type {
                                        ident: `E1`,
                                    },
                                ),
                            },
                            SynInheritedSymbol {
                                parent_symbol_idx: Current(
                                    4,
                                ),
                                modifier: Const,
                                kind: SynInheritedSymbolKind::TemplateParameter(
                                    InheritedTemplateParameterSynSymbol::Type {
                                        ident: `E2`,
                                    },
                                ),
                            },
                            SynInheritedSymbol {
                                parent_symbol_idx: Current(
                                    1,
                                ),
                                modifier: None,
                                kind: SynInheritedSymbolKind::ParenateParameter {
                                    ident: `result`,
                                },
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
                        kind: EvalExpr,
                        syn_expr_idx: 1,
                    },
                    SynExprRoot {
                        kind: BlockExpr,
                        syn_expr_idx: 2,
                    },
                ],
                has_self_lifetime: false,
                has_self_place: false,
            },
        },
        data: SemaExprRegionData {
            path: Defn(
                AssociatedItem(
                    TraitForTypeItem(
                        TraitForTypeItemSynNodePath(
                            Id {
                                value: 17,
                            },
                        ),
                    ),
                ),
            ),
            sema_expr_arena: SemaExprArena(
                Arena {
                    data: [
                        SemaExprEntry {
                            data_result: Ok(
                                Todo {
                                    regional_token_idx: RegionalTokenIdx(
                                        1,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        EntityPath(
                                            TypeOntology(
                                                TypePath(
                                                    Id {
                                                        value: 3,
                                                    },
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            ),
                        },
                        SemaExprEntry {
                            data_result: Ok(
                                Block {
                                    stmts: SemaStmtIdxRange(
                                        ArenaIdxRange(
                                            1..2,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        EntityPath(
                                            TypeOntology(
                                                TypePath(
                                                    Id {
                                                        value: 3,
                                                    },
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sema_stmt_arena: SemaStmtArena(
                Arena {
                    data: [
                        SemaStmtEntry {
                            data_result: Ok(
                                Eval {
                                    sema_expr_idx: SemaExprIdx(
                                        1,
                                    ),
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        EntityPath(
                                            TypeOntology(
                                                TypePath(
                                                    Id {
                                                        value: 3,
                                                    },
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sema_expr_roots: [
                (
                    2,
                    (
                        SemaExprIdx(
                            2,
                        ),
                        BlockExpr,
                    ),
                ),
            ],
            pattern_expr_ty_infos: ArenaMap {
                data: [],
            },
            pattern_symbol_ty_infos: ArenaMap {
                data: [],
            },
            sema_expr_terms: [],
            symbol_tys: SymbolMap {
                inherited_symbol_map: ArenaMap {
                    data: [
                        Some(
                            SymbolType(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        Category(
                                            TermCategory {
                                                universe: TermUniverse(
                                                    1,
                                                ),
                                            },
                                        ),
                                    ),
                                },
                            ),
                        ),
                        Some(
                            SymbolType(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        Category(
                                            TermCategory {
                                                universe: TermUniverse(
                                                    1,
                                                ),
                                            },
                                        ),
                                    ),
                                },
                            ),
                        ),
                        Some(
                            SymbolType(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        Category(
                                            TermCategory {
                                                universe: TermUniverse(
                                                    1,
                                                ),
                                            },
                                        ),
                                    ),
                                },
                            ),
                        ),
                        Some(
                            SymbolType(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        Category(
                                            TermCategory {
                                                universe: TermUniverse(
                                                    1,
                                                ),
                                            },
                                        ),
                                    ),
                                },
                            ),
                        ),
                        Some(
                            SymbolType(
                                FluffyTerm {
                                    place: None,
                                    base: Ethereal(
                                        Application(
                                            EtherealTermApplication(
                                                Id {
                                                    value: 4,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            ),
                        ),
                    ],
                },
                current_symbol_map: ArenaMap {
                    data: [],
                },
            },
            symbol_terms: SymbolMap {
                inherited_symbol_map: ArenaMap {
                    data: [
                        Some(
                            FluffyTerm {
                                place: None,
                                base: Ethereal(
                                    Symbol(
                                        EtherealTermSymbol(
                                            Id {
                                                value: 1,
                                            },
                                        ),
                                    ),
                                ),
                            },
                        ),
                        Some(
                            FluffyTerm {
                                place: None,
                                base: Ethereal(
                                    Symbol(
                                        EtherealTermSymbol(
                                            Id {
                                                value: 3,
                                            },
                                        ),
                                    ),
                                ),
                            },
                        ),
                        Some(
                            FluffyTerm {
                                place: None,
                                base: Ethereal(
                                    Symbol(
                                        EtherealTermSymbol(
                                            Id {
                                                value: 2,
                                            },
                                        ),
                                    ),
                                ),
                            },
                        ),
                        Some(
                            FluffyTerm {
                                place: None,
                                base: Ethereal(
                                    Symbol(
                                        EtherealTermSymbol(
                                            Id {
                                                value: 4,
                                            },
                                        ),
                                    ),
                                ),
                            },
                        ),
                        None,
                    ],
                },
                current_symbol_map: ArenaMap {
                    data: [],
                },
            },
            fluffy_term_region: FluffyTermRegion {
                terms: FluffyTerms {
                    solid_terms: SolidTerms {
                        entries: VecSet {
                            data: [],
                        },
                    },
                    hollow_terms: HollowTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FluffyTermExpectationEntry {
                                expectation: ImplicitlyConvertible(
                                    ExpectCoersion {
                                        contract: Move,
                                        ty_expected: FluffyTerm {
                                            place: None,
                                            base: Ethereal(
                                                Application(
                                                    EtherealTermApplication(
                                                        Id {
                                                            value: 2,
                                                        },
                                                    ),
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                meta: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FluffyTerm {
                                        place: None,
                                        base: Ethereal(
                                            EntityPath(
                                                TypeOntology(
                                                    TypePath(
                                                        Id {
                                                            value: 3,
                                                        },
                                                    ),
                                                ),
                                            ),
                                        ),
                                    },
                                    resolve_progress: Resolved(
                                        Ok(
                                            ImplicitlyConvertible(
                                                Never,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FluffyTermExpectationEntry {
                                expectation: ImplicitlyConvertible(
                                    ExpectCoersion {
                                        contract: Move,
                                        ty_expected: FluffyTerm {
                                            place: None,
                                            base: Ethereal(
                                                Application(
                                                    EtherealTermApplication(
                                                        Id {
                                                            value: 2,
                                                        },
                                                    ),
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                meta: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FluffyTerm {
                                        place: None,
                                        base: Ethereal(
                                            EntityPath(
                                                TypeOntology(
                                                    TypePath(
                                                        Id {
                                                            value: 3,
                                                        },
                                                    ),
                                                ),
                                            ),
                                        ),
                                    },
                                    resolve_progress: Resolved(
                                        Ok(
                                            ImplicitlyConvertible(
                                                Never,
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: Some(
                Application(
                    EtherealTermApplication(
                        Id {
                            value: 2,
                        },
                    ),
                ),
            ),
            self_ty: Some(
                Application(
                    EtherealTermApplication(
                        Id {
                            value: 2,
                        },
                    ),
                ),
            ),
        },
    },
]