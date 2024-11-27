```rust
[
    (
        ItemPath(`mnist_classifier::digits::one::one_fermi_match`),
        Some(
            ItemSynDefn {
                body: 7,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::one::one_fermi_match`, `Val`, (0)),
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 0,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `FermiMatchResult`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            4,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_region: SynPatternRegion {
                                        pattern_arena: Arena {
                                            data: [],
                                        },
                                        pattern_contracts: [],
                                        pattern_variable_arena: Arena {
                                            data: [],
                                        },
                                        pattern_variable_maps: [],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    variable_region: VariableRegionData {
                                        inherited_variable_arena: Arena {
                                            data: [],
                                        },
                                        current_variable_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: False,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [],
                                    },
                                    pattern_roots: [],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 0,
                                        },
                                    ],
                                    has_self_lifetime: false,
                                    has_self_place: false,
                                    pattern_to_current_variable_map: [],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::digits::one::one_fermi_match`, `Val`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                                    Fn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 2,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::downmost`, `Ritchie(
                                                    Fn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 3,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::upmost`, `Ritchie(
                                                    Fn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 4,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::hat`, `Ritchie(
                                                    Fn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::List {
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 2,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    7,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 3,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    9,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 4,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        11,
                                    ),
                                },
                                SynExprData::FunctionApplicationOrCall {
                                    function: 0,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 1,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    4,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 5,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        12,
                                    ),
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        0..1,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                1,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_concave_components`,
                                            regional_token_idx: RegionalTokenIdx(
                                                3,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `downmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                6,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::downmost`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `upmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                8,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::upmost`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `hat`,
                                            regional_token_idx: RegionalTokenIdx(
                                                10,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::hat`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                            ],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Eval {
                                    expr_idx: 6,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                            ],
                        },
                        pattern_region: SynPatternRegion {
                            pattern_arena: Arena {
                                data: [],
                            },
                            pattern_contracts: [],
                            pattern_variable_arena: Arena {
                                data: [],
                            },
                            pattern_variable_maps: [],
                            pattern_variable_modifiers: ArenaMap {
                                data: [],
                            },
                        },
                        variable_region: VariableRegionData {
                            inherited_variable_arena: Arena {
                                data: [],
                            },
                            current_variable_arena: Arena {
                                data: [],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 6,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 7,
                            },
                        ],
                        has_self_lifetime: false,
                        has_self_place: false,
                        pattern_to_current_variable_map: [],
                    },
                },
            },
        ),
    ),
    (
        ItemPath(`mnist_classifier::digits::one::is_one`),
        Some(
            ItemSynDefn {
                body: 248,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::one::is_one`, `Val`, (0)),
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 0,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`mnist::MnistLabel`, `Enum`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::ExplicitApplication {
                                                function_expr_idx: 0,
                                                argument_expr_idx: 1,
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 3,
                                                opt_path: Some(
                                                    PrincipalEntityPath::TypeVariant(
                                                        TypeVariantPath(`mnist::MnistLabel::One`),
                                                    ),
                                                ),
                                            },
                                            SynExprData::ExplicitApplication {
                                                function_expr_idx: 2,
                                                argument_expr_idx: 3,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `OneVsAll`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`malamute::OneVsAll`, `Enum`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `MnistLabel`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            6,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist::MnistLabel`, `Enum`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `MnistLabel`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist::MnistLabel`, `Enum`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Subitem {
                                                parent: 2,
                                                colon_colon_token: ColonColonRegionalToken(
                                                    RegionalTokenIdx(
                                                        8,
                                                    ),
                                                ),
                                                ident_token: Ok(
                                                    IdentRegionalToken {
                                                        ident: `One`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            9,
                                                        ),
                                                    },
                                                ),
                                                path: Ok(
                                                    PrincipalEntityPath::TypeVariant(
                                                        TypeVariantPath(`mnist::MnistLabel::One`),
                                                    ),
                                                ),
                                            },
                                        ],
                                    },
                                    stmt_arena: Arena {
                                        data: [],
                                    },
                                    pattern_region: SynPatternRegion {
                                        pattern_arena: Arena {
                                            data: [],
                                        },
                                        pattern_contracts: [],
                                        pattern_variable_arena: Arena {
                                            data: [],
                                        },
                                        pattern_variable_maps: [],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [],
                                        },
                                    },
                                    variable_region: VariableRegionData {
                                        inherited_variable_arena: Arena {
                                            data: [],
                                        },
                                        current_variable_arena: Arena {
                                            data: [],
                                        },
                                        allow_self_type: False,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [],
                                    },
                                    pattern_roots: [],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 4,
                                        },
                                    ],
                                    has_self_lifetime: false,
                                    has_self_place: false,
                                    pattern_to_current_variable_map: [],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::digits::one::is_one`, `Val`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 1,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max_hole_ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            5,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 2,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        11,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            5,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 0,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 2,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        6,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 3,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        8,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    9,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 4,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        12,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 5,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        14,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 3,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                                    Fn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 4,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::List {
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        22,
                                    ),
                                    items: [],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        23,
                                    ),
                                },
                                SynExprData::FunctionApplicationOrCall {
                                    function: 7,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 8,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    21,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 9,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        24,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_one_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        26,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 11,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            28,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        30,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 15,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 12,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        29,
                                    ),
                                    ropd: 13,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 5,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 6,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 16,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        35,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max_row_span`,
                                        regional_token_idx: RegionalTokenIdx(
                                            36,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        40,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            5,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 15,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        33,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 17,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        37,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    38,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 18,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        41,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        42,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 19,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        43,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 7,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 21,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        46,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max_row_span`,
                                        regional_token_idx: RegionalTokenIdx(
                                            47,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        49,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 17,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 22,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Greater,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        48,
                                    ),
                                    ropd: 23,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 8,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 25,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        53,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max_hole_ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            54,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        56,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 26,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        55,
                                    ),
                                    ropd: 27,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 10,
                                    opt_path: Some(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 11,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 30,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        64,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max_hole_ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            65,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        67,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 31,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        66,
                                    ),
                                    ropd: 32,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 12,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        71,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 34,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        70,
                                    ),
                                    ropd: 35,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 14,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 37,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        76,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            77,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        79,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 38,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        78,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 39,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        80,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 16,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 41,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        85,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            86,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        88,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 42,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        87,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 43,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        89,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 18,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 45,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        94,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            95,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        97,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 46,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        96,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 47,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        98,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        100,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Be {
                                    src: 49,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        101,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 4,
                                            },
                                            variables: ArenaIdxRange(
                                                4..4,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_one_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        105,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 51,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        106,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            107,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        109,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 18,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 52,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        108,
                                    ),
                                    ropd: 53,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 20,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_one_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        112,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 56,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        113,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            114,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 57,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        115,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `abs`,
                                        regional_token_idx: RegionalTokenIdx(
                                            116,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        117,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        118,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        122,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            5,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 55,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        111,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 58,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        119,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    120,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 59,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        123,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        124,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 60,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        125,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 21,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        127,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 4,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Field {
                                    owner: 62,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        130,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `lower_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            131,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 22,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 63,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Mul,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        128,
                                    ),
                                    ropd: 64,
                                },
                                SynExprData::Field {
                                    owner: 65,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        134,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `upper_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            135,
                                        ),
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 66,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        132,
                                    ),
                                    ropd: 67,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        137,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 19,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 68,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        136,
                                    ),
                                    ropd: 69,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 24,
                                    opt_path: Some(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        145,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 72,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        146,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 73,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        147,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            148,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        154,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 75,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        155,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 76,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        156,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            157,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 74,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        149,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            150,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        151,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        152,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 77,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        158,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            159,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        160,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        161,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 78,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        153,
                                    ),
                                    ropd: 79,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 25,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 81,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        164,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            165,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        167,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 6,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 82,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        166,
                                    ),
                                    ropd: 83,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 26,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 27,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        174,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            3,
                                        ),
                                    ),
                                ),
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 86,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        171,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `top_k_row_span_sum`,
                                        regional_token_idx: RegionalTokenIdx(
                                            172,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        173,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 87,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        175,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 28,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 89,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        178,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            179,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 29,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 91,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        182,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rel_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            183,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 30,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 93,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        186,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            187,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        191,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            12,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 85,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        169,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 88,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        176,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 90,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        180,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 92,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        184,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 94,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        188,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    189,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 95,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        192,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        193,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 96,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        194,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 31,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 32,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 99,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        198,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            199,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        201,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 100,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        200,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 101,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        202,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 102,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        203,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 103,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        204,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rel_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            205,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 33,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 105,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        208,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            209,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        211,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 106,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        210,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 107,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        212,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 108,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        213,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 109,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        214,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change`,
                                        regional_token_idx: RegionalTokenIdx(
                                            215,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 110,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        216,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `abs`,
                                        regional_token_idx: RegionalTokenIdx(
                                            217,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        218,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        219,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        223,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 98,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        196,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 104,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        206,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 111,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        220,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    221,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 112,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        224,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        225,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 113,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        226,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        228,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Be {
                                    src: 115,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        229,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 7,
                                            },
                                            variables: ArenaIdxRange(
                                                5..5,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        236,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 117,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        237,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 118,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        238,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            239,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        245,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 120,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        246,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 121,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        247,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            248,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 119,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        240,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            241,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        242,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        243,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 122,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        249,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            250,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        251,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        252,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 123,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        244,
                                    ),
                                    ropd: 124,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        254,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 125,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        253,
                                    ),
                                    ropd: 126,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        258,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 128,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        259,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 129,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        260,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            261,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        263,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 131,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        264,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 132,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        265,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            266,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 133,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        267,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            268,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        269,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        270,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        272,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 134,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Add,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        271,
                                    ),
                                    ropd: 135,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 130,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        262,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 136,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        273,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `long_vertical`,
                                    regional_token_idx: RegionalTokenIdx(
                                        277,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 6,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 138,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        278,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            279,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        280,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        281,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `long_vertical_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        283,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 140,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        284,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            285,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        287,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 141,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Greater,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        286,
                                    ),
                                    ropd: 142,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 35,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        290,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 145,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        291,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 146,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        292,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            293,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        295,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 148,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        296,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 149,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        297,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rel_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            298,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `upmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        300,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 151,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        301,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 152,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        302,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change`,
                                        regional_token_idx: RegionalTokenIdx(
                                            303,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 153,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        304,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `abs`,
                                        regional_token_idx: RegionalTokenIdx(
                                            305,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        306,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        307,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        311,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 144,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        289,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 147,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        294,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 150,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        299,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 154,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        308,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    309,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 155,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        312,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        313,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 156,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        314,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 36,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `long_vertical_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        317,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 159,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        318,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            319,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        320,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        321,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `long_vertical_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        323,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `long_vertical_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        327,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 161,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        324,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `x`,
                                        regional_token_idx: RegionalTokenIdx(
                                            325,
                                        ),
                                    },
                                },
                                SynExprData::Field {
                                    owner: 162,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        328,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            329,
                                        ),
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 163,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Div,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        326,
                                    ),
                                    ropd: 164,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        333,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 158,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        316,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 160,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        322,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 165,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        330,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    331,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 166,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        334,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        335,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 167,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        336,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `hat`,
                                    regional_token_idx: RegionalTokenIdx(
                                        338,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Be {
                                    src: 169,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        339,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 11,
                                            },
                                            variables: ArenaIdxRange(
                                                7..7,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 38,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 39,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 172,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        348,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            349,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        351,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 173,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        350,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 174,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        352,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 175,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        353,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 176,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        354,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            355,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 40,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 178,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        358,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            359,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        361,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 179,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        360,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 180,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        362,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 181,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        363,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 182,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        364,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rel_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            365,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 41,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 184,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        368,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            369,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        371,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 185,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        370,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 186,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        372,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 187,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        373,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 188,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        374,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change`,
                                        regional_token_idx: RegionalTokenIdx(
                                            375,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 189,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        376,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `abs`,
                                        regional_token_idx: RegionalTokenIdx(
                                            377,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        378,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        379,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        383,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 171,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        346,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 177,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        356,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 183,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        366,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 190,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        380,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    381,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 191,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        384,
                                                    ),
                                                ),
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        385,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 192,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        386,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_number_of_strokes`,
                                    regional_token_idx: RegionalTokenIdx(
                                        388,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 4,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        390,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            3,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 194,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        389,
                                    ),
                                    ropd: 195,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        394,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 197,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        395,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 198,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        396,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            397,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        399,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 200,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        400,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 201,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        401,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            402,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 202,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        403,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            404,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        405,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        406,
                                    ),
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 199,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        398,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 203,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        407,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_hat`,
                                    regional_token_idx: RegionalTokenIdx(
                                        411,
                                    ),
                                    current_variable_idx: 7,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 9,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 205,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        412,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            413,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        414,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        415,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        419,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 207,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        420,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 208,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        421,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            422,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost`,
                                    regional_token_idx: RegionalTokenIdx(
                                        424,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 210,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        425,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 211,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        426,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            427,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 212,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        428,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            429,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        430,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        431,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        433,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            2,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 213,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Add,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        432,
                                    ),
                                    ropd: 214,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 209,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        423,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 215,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        434,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_feet`,
                                    regional_token_idx: RegionalTokenIdx(
                                        438,
                                    ),
                                    current_variable_idx: 9,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 11,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 217,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        439,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            440,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        441,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        442,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 42,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                    Gn,
                                                )`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_hat_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        445,
                                    ),
                                    current_variable_idx: 8,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 10,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 220,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        446,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            447,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_feet_dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        449,
                                    ),
                                    current_variable_idx: 10,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 12,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 222,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        450,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            451,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        455,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            5,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 219,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        444,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 221,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        448,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 223,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        452,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    453,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 224,
                                                separator: CallListSeparator::None,
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        456,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 225,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        457,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `downmost_number_of_strokes`,
                                    regional_token_idx: RegionalTokenIdx(
                                        459,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 4,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        461,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            3,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 227,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        460,
                                    ),
                                    ropd: 228,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 43,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 230,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        466,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `lower_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            467,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 44,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 232,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        472,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `upper_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            473,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `a`,
                                    regional_token_idx: RegionalTokenIdx(
                                        477,
                                    ),
                                    current_variable_idx: 11,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 13,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `b`,
                                    regional_token_idx: RegionalTokenIdx(
                                        479,
                                    ),
                                    current_variable_idx: 12,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 14,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 234,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        478,
                                    ),
                                    ropd: 235,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `c`,
                                    regional_token_idx: RegionalTokenIdx(
                                        483,
                                    ),
                                    current_variable_idx: 13,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 15,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `a`,
                                    regional_token_idx: RegionalTokenIdx(
                                        485,
                                    ),
                                    current_variable_idx: 11,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 13,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 237,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Add,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        484,
                                    ),
                                    ropd: 238,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        490,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 20,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::CurrentVariable {
                                    ident: `c`,
                                    regional_token_idx: RegionalTokenIdx(
                                        487,
                                    ),
                                    current_variable_idx: 13,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 15,
                                    },
                                },
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        489,
                                    ),
                                    opd: 240,
                                },
                                SynExprData::Binary {
                                    lopd: 241,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Geq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        488,
                                    ),
                                    ropd: 242,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `c`,
                                    regional_token_idx: RegionalTokenIdx(
                                        492,
                                    ),
                                    current_variable_idx: 13,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 15,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        494,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 21,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 244,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Leq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        493,
                                    ),
                                    ropd: 245,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 46,
                                    opt_path: Some(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        41..44,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                1,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                3,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `ignored_connected_components_row_span_sum_sum`,
                                            regional_token_idx: RegionalTokenIdx(
                                                7,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                18,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_concave_components`,
                                            regional_token_idx: RegionalTokenIdx(
                                                20,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                32,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                34,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                45,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                52,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `OneVsAll`,
                                            regional_token_idx: RegionalTokenIdx(
                                                57,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Subitem {
                                    parent: 9,
                                    colon_colon_token: ColonColonRegionalToken(
                                        RegionalTokenIdx(
                                            58,
                                        ),
                                    ),
                                    ident_token: Ok(
                                        IdentRegionalToken {
                                            ident: `Yes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                59,
                                            ),
                                        },
                                    ),
                                    path: Ok(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                63,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `ignored_connected_components_row_span_sum_sum`,
                                            regional_token_idx: RegionalTokenIdx(
                                                69,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `downmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                73,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::downmost`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                75,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `upmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                82,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::upmost`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                84,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `hat`,
                                            regional_token_idx: RegionalTokenIdx(
                                                91,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::hat`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                93,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `None`,
                                            regional_token_idx: RegionalTokenIdx(
                                                102,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::TypeVariant(
                                        TypeVariantPath(`core::option::Option::None`),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                110,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                129,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                133,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `OneVsAll`,
                                            regional_token_idx: RegionalTokenIdx(
                                                139,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Subitem {
                                    parent: 23,
                                    colon_colon_token: ColonColonRegionalToken(
                                        RegionalTokenIdx(
                                            140,
                                        ),
                                    ),
                                    ident_token: Ok(
                                        IdentRegionalToken {
                                            ident: `Yes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                141,
                                            ),
                                        },
                                    ),
                                    path: Ok(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                163,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                168,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                170,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                177,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                181,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                185,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                195,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                197,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                207,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `Some`,
                                            regional_token_idx: RegionalTokenIdx(
                                                230,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::TypeVariant(
                                        TypeVariantPath(`core::option::Option::Some`),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                288,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                315,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `Some`,
                                            regional_token_idx: RegionalTokenIdx(
                                                340,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::TypeVariant(
                                        TypeVariantPath(`core::option::Option::Some`),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                345,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                347,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                357,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `one_fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                367,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::one::one_fermi_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `narrow_down`,
                                            regional_token_idx: RegionalTokenIdx(
                                                443,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`malamute::narrow_down`, `Ritchie(
                                                Gn,
                                            )`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                465,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                471,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `OneVsAll`,
                                            regional_token_idx: RegionalTokenIdx(
                                                495,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Subitem {
                                    parent: 45,
                                    colon_colon_token: ColonColonRegionalToken(
                                        RegionalTokenIdx(
                                            496,
                                        ),
                                    ),
                                    ident_token: Ok(
                                        IdentRegionalToken {
                                            ident: `Yes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                497,
                                            ),
                                        },
                                    ),
                                    path: Ok(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                            ],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            51,
                                        ),
                                    },
                                    condition: 28,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 20,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                44,
                                            ),
                                        },
                                        condition: Ok(
                                            24,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    50,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            0..1,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 29,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            104,
                                        ),
                                    },
                                    condition: 54,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 61,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            126,
                                        ),
                                    },
                                    condition: 70,
                                },
                                SynStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            138,
                                        ),
                                    },
                                    result: 71,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            235,
                                        ),
                                    },
                                    condition: 127,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            255,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 8,
                                            },
                                            variables: ArenaIdxRange(
                                                5..6,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                257,
                                            ),
                                        ),
                                    ),
                                    initial_value: 137,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            274,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 9,
                                            },
                                            variables: ArenaIdxRange(
                                                6..7,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                276,
                                            ),
                                        ),
                                    ),
                                    initial_value: 139,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            282,
                                        ),
                                    },
                                    condition: 143,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 157,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Eval {
                                    expr_idx: 168,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Eval {
                                    expr_idx: 193,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            62,
                                        ),
                                    },
                                    condition: 33,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            68,
                                        ),
                                    },
                                    condition: 36,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            72,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 1,
                                            },
                                            variables: ArenaIdxRange(
                                                1..2,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                74,
                                            ),
                                        ),
                                    ),
                                    initial_value: 40,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            81,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 2,
                                            },
                                            variables: ArenaIdxRange(
                                                2..3,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                83,
                                            ),
                                        ),
                                    ),
                                    initial_value: 44,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            90,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 3,
                                            },
                                            variables: ArenaIdxRange(
                                                3..4,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                92,
                                            ),
                                        ),
                                    ),
                                    initial_value: 48,
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                99,
                                            ),
                                        },
                                        condition: Ok(
                                            50,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    103,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            4..8,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            142,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 5,
                                            },
                                            variables: ArenaIdxRange(
                                                4..5,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                144,
                                            ),
                                        ),
                                    ),
                                    initial_value: 80,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            162,
                                        ),
                                    },
                                    condition: 84,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 97,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Eval {
                                    expr_idx: 114,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                227,
                                            ),
                                        },
                                        condition: Ok(
                                            116,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    234,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            8..14,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                337,
                                            ),
                                        },
                                        condition: Ok(
                                            170,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    344,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            14..15,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            387,
                                        ),
                                    },
                                    condition: 196,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            391,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 12,
                                            },
                                            variables: ArenaIdxRange(
                                                7..8,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                393,
                                            ),
                                        ),
                                    ),
                                    initial_value: 204,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            408,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 13,
                                            },
                                            variables: ArenaIdxRange(
                                                8..9,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                410,
                                            ),
                                        ),
                                    ),
                                    initial_value: 206,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            416,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 14,
                                            },
                                            variables: ArenaIdxRange(
                                                9..10,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                418,
                                            ),
                                        ),
                                    ),
                                    initial_value: 216,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            435,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 15,
                                            },
                                            variables: ArenaIdxRange(
                                                10..11,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                437,
                                            ),
                                        ),
                                    ),
                                    initial_value: 218,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 226,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            458,
                                        ),
                                    },
                                    condition: 229,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            462,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 16,
                                            },
                                            variables: ArenaIdxRange(
                                                11..12,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                464,
                                            ),
                                        ),
                                    ),
                                    initial_value: 231,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            468,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 17,
                                            },
                                            variables: ArenaIdxRange(
                                                12..13,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                470,
                                            ),
                                        ),
                                    ),
                                    initial_value: 233,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            474,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 18,
                                            },
                                            variables: ArenaIdxRange(
                                                13..14,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                476,
                                            ),
                                        ),
                                    ),
                                    initial_value: 236,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            480,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 19,
                                            },
                                            variables: ArenaIdxRange(
                                                14..15,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                482,
                                            ),
                                        ),
                                    ),
                                    initial_value: 239,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            486,
                                        ),
                                    },
                                    condition: 243,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            491,
                                        ),
                                    },
                                    condition: 246,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 247,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Eval {
                                    expr_idx: 6,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            15,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 0,
                                            },
                                            variables: ArenaIdxRange(
                                                0..1,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                17,
                                            ),
                                        ),
                                    ),
                                    initial_value: 10,
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                25,
                                            ),
                                        },
                                        condition: Ok(
                                            14,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    31,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            1..4,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: Some(
                                        SynElseBranch {
                                            else_token: ElseRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    60,
                                                ),
                                            },
                                            eol_colon_token: Ok(
                                                EolColonRegionalToken {
                                                    regional_token_idx: RegionalTokenIdx(
                                                        61,
                                                    ),
                                                },
                                            ),
                                            stmts: ArenaIdxRange(
                                                15..41,
                                            ),
                                        },
                                    ),
                                },
                            ],
                        },
                        pattern_region: SynPatternRegion {
                            pattern_arena: Arena {
                                data: [
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `simp_one_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                16,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                73,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `upmost`,
                                            regional_token_idx: RegionalTokenIdx(
                                                82,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `hat`,
                                            regional_token_idx: RegionalTokenIdx(
                                                91,
                                            ),
                                        },
                                    },
                                    SynPatternData::UnitTypeVariant {
                                        path_expr_idx: 19,
                                        path: TypeVariantPath(`core::option::Option::None`),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost_number_of_strokes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                143,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `_`,
                                            regional_token_idx: RegionalTokenIdx(
                                                232,
                                            ),
                                        },
                                    },
                                    SynPatternData::TupleTypeVariant {
                                        path_expr_idx: 34,
                                        path: TypeVariantPath(`core::option::Option::Some`),
                                        lpar: LparRegionalToken(
                                            RegionalTokenIdx(
                                                231,
                                            ),
                                        ),
                                        fields: PunctuatedSmallList {
                                            elements: [
                                                SynPatternComponent(
                                                    6,
                                                ),
                                            ],
                                            separators: [],
                                            phantom: PhantomData<husky_syn_expr::error::SynExprError>,
                                        },
                                        rpar: RparRegionalToken(
                                            RegionalTokenIdx(
                                                233,
                                            ),
                                        ),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `long_vertical`,
                                            regional_token_idx: RegionalTokenIdx(
                                                256,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `long_vertical_dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                275,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `_`,
                                            regional_token_idx: RegionalTokenIdx(
                                                342,
                                            ),
                                        },
                                    },
                                    SynPatternData::TupleTypeVariant {
                                        path_expr_idx: 37,
                                        path: TypeVariantPath(`core::option::Option::Some`),
                                        lpar: LparRegionalToken(
                                            RegionalTokenIdx(
                                                341,
                                            ),
                                        ),
                                        fields: PunctuatedSmallList {
                                            elements: [
                                                SynPatternComponent(
                                                    10,
                                                ),
                                            ],
                                            separators: [],
                                            phantom: PhantomData<husky_syn_expr::error::SynExprError>,
                                        },
                                        rpar: RparRegionalToken(
                                            RegionalTokenIdx(
                                                343,
                                            ),
                                        ),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost_hat`,
                                            regional_token_idx: RegionalTokenIdx(
                                                392,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost_hat_dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                409,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost_feet`,
                                            regional_token_idx: RegionalTokenIdx(
                                                417,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `downmost_feet_dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                436,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `a`,
                                            regional_token_idx: RegionalTokenIdx(
                                                463,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `b`,
                                            regional_token_idx: RegionalTokenIdx(
                                                469,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `c`,
                                            regional_token_idx: RegionalTokenIdx(
                                                475,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `d`,
                                            regional_token_idx: RegionalTokenIdx(
                                                481,
                                            ),
                                        },
                                    },
                                ],
                            },
                            pattern_contracts: [
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Pure,
                            ],
                            pattern_variable_arena: Arena {
                                data: [
                                    PatternVariable::Atom(
                                        0,
                                    ),
                                    PatternVariable::Atom(
                                        1,
                                    ),
                                    PatternVariable::Atom(
                                        2,
                                    ),
                                    PatternVariable::Atom(
                                        3,
                                    ),
                                    PatternVariable::Atom(
                                        5,
                                    ),
                                    PatternVariable::Atom(
                                        6,
                                    ),
                                    PatternVariable::Atom(
                                        8,
                                    ),
                                    PatternVariable::Atom(
                                        9,
                                    ),
                                    PatternVariable::Atom(
                                        10,
                                    ),
                                    PatternVariable::Atom(
                                        12,
                                    ),
                                    PatternVariable::Atom(
                                        13,
                                    ),
                                    PatternVariable::Atom(
                                        14,
                                    ),
                                    PatternVariable::Atom(
                                        15,
                                    ),
                                    PatternVariable::Atom(
                                        16,
                                    ),
                                    PatternVariable::Atom(
                                        17,
                                    ),
                                    PatternVariable::Atom(
                                        18,
                                    ),
                                    PatternVariable::Atom(
                                        19,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `simp_one_match`,
                                        0,
                                    ),
                                ],
                                [
                                    (
                                        `downmost`,
                                        1,
                                    ),
                                ],
                                [
                                    (
                                        `upmost`,
                                        2,
                                    ),
                                ],
                                [
                                    (
                                        `hat`,
                                        3,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `downmost_number_of_strokes`,
                                        4,
                                    ),
                                ],
                                [
                                    (
                                        `_`,
                                        5,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `long_vertical`,
                                        6,
                                    ),
                                ],
                                [
                                    (
                                        `long_vertical_dp`,
                                        7,
                                    ),
                                ],
                                [
                                    (
                                        `_`,
                                        8,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `downmost_hat`,
                                        9,
                                    ),
                                ],
                                [
                                    (
                                        `downmost_hat_dp`,
                                        10,
                                    ),
                                ],
                                [
                                    (
                                        `downmost_feet`,
                                        11,
                                    ),
                                ],
                                [
                                    (
                                        `downmost_feet_dp`,
                                        12,
                                    ),
                                ],
                                [
                                    (
                                        `a`,
                                        13,
                                    ),
                                ],
                                [
                                    (
                                        `b`,
                                        14,
                                    ),
                                ],
                                [
                                    (
                                        `c`,
                                        15,
                                    ),
                                ],
                                [
                                    (
                                        `d`,
                                        16,
                                    ),
                                ],
                            ],
                            pattern_variable_modifiers: ArenaMap {
                                data: [
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                    Pure,
                                ],
                            },
                        },
                        variable_region: VariableRegionData {
                            inherited_variable_arena: Arena {
                                data: [],
                            },
                            current_variable_arena: Arena {
                                data: [
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            17,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `simp_one_match`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            74,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost`,
                                            pattern_variable_idx: 1,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            83,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `upmost`,
                                            pattern_variable_idx: 2,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            92,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `hat`,
                                            pattern_variable_idx: 3,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            144,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost_number_of_strokes`,
                                            pattern_variable_idx: 4,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            257,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    337,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `long_vertical`,
                                            pattern_variable_idx: 6,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            276,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    337,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `long_vertical_dp`,
                                            pattern_variable_idx: 7,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            393,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost_hat`,
                                            pattern_variable_idx: 9,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            410,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost_hat_dp`,
                                            pattern_variable_idx: 10,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            418,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost_feet`,
                                            pattern_variable_idx: 11,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            437,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `downmost_feet_dp`,
                                            pattern_variable_idx: 12,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            464,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `a`,
                                            pattern_variable_idx: 13,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            470,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `b`,
                                            pattern_variable_idx: 14,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            476,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `c`,
                                            pattern_variable_idx: 15,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            482,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    498,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `d`,
                                            pattern_variable_idx: 16,
                                        },
                                    },
                                ],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 0,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 1,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 2,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 3,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Be,
                                syn_pattern_idx: 4,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 5,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Be,
                                syn_pattern_idx: 7,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 8,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 9,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Be,
                                syn_pattern_idx: 11,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 12,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 13,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 14,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 15,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 16,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 17,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 18,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 19,
                            },
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 6,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 10,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 20,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 28,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 29,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 33,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 36,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 40,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 44,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 48,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 54,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 61,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 70,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::ReturnExpr,
                                syn_expr_idx: 71,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 80,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 84,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 97,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 114,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 127,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 137,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 139,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 143,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 157,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 168,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 193,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 196,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 204,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 206,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 216,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 218,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 226,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 229,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 231,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 233,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 236,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 239,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 243,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 246,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 247,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 248,
                            },
                        ],
                        has_self_lifetime: false,
                        has_self_place: false,
                        pattern_to_current_variable_map: [
                            (
                                0,
                                0,
                            ),
                            (
                                1,
                                1,
                            ),
                            (
                                2,
                                2,
                            ),
                            (
                                3,
                                3,
                            ),
                            (
                                4,
                                4,
                            ),
                            (
                                6,
                                5,
                            ),
                            (
                                7,
                                6,
                            ),
                            (
                                9,
                                7,
                            ),
                            (
                                10,
                                8,
                            ),
                            (
                                11,
                                9,
                            ),
                            (
                                12,
                                10,
                            ),
                            (
                                13,
                                11,
                            ),
                            (
                                14,
                                12,
                            ),
                            (
                                15,
                                13,
                            ),
                            (
                                16,
                                14,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
    (
        ItemPath(`mnist_classifier::digits::one::upmost`),
        Some(
            ItemSynDefn {
                body: 8,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::one::upmost`, `Ritchie(
                                                    Fn,
                                                )`, (0)),
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 0,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Tilde,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                                opd: 0,
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::f32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Option,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    10,
                                                ),
                                                opd: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `ConcaveComponent`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `f32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            11,
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
                                    pattern_region: SynPatternRegion {
                                        pattern_arena: Arena {
                                            data: [
                                                SynPatternData::Ident {
                                                    symbol_modifier_tokens: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `cc`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            4,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_contracts: [
                                            Contract::Pure,
                                        ],
                                        pattern_variable_arena: Arena {
                                            data: [
                                                PatternVariable::Atom(
                                                    0,
                                                ),
                                            ],
                                        },
                                        pattern_variable_maps: [
                                            [
                                                (
                                                    `cc`,
                                                    0,
                                                ),
                                            ],
                                        ],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [
                                                Pure,
                                            ],
                                        },
                                    },
                                    variable_region: VariableRegionData {
                                        inherited_variable_arena: Arena {
                                            data: [],
                                        },
                                        current_variable_arena: Arena {
                                            data: [
                                                CurrentVariableEntry {
                                                    modifier: Pure,
                                                    access_start: RegionalTokenIdx(
                                                        5,
                                                    ),
                                                    access_end: None,
                                                    data: CurrentVariableData::SimpleParenateParameter {
                                                        ident: `cc`,
                                                        pattern_variable_idx: 0,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: False,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [
                                            (
                                                SimpleParenateParameter {
                                                    syn_pattern_root: ParenateParameterSynPatternRoot {
                                                        syn_pattern_idx: 0,
                                                    },
                                                    ty: 1,
                                                },
                                                ArenaIdxRange(
                                                    0..1,
                                                ),
                                            ),
                                        ],
                                    },
                                    pattern_roots: [
                                        SynPatternRoot {
                                            kind: SynPatternRootKind::Parenate,
                                            syn_pattern_idx: 0,
                                        },
                                    ],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ExplicitParameterType,
                                            syn_expr_idx: 1,
                                        },
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 3,
                                        },
                                    ],
                                    has_self_lifetime: false,
                                    has_self_place: false,
                                    pattern_to_current_variable_map: [
                                        (
                                            0,
                                            0,
                                        ),
                                    ],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::digits::one::upmost`, `Ritchie(
                                        Fn,
                                    )`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 2,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        11,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        14,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 3,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Greater,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                    ropd: 4,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 6,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        16,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            17,
                                        ),
                                    },
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        0..3,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 0,
                                            },
                                            variables: ArenaIdxRange(
                                                0..1,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                3,
                                            ),
                                        ),
                                    ),
                                    initial_value: 1,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            9,
                                        ),
                                    },
                                    condition: 5,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 7,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                            ],
                        },
                        pattern_region: SynPatternRegion {
                            pattern_arena: Arena {
                                data: [
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                2,
                                            ),
                                        },
                                    },
                                ],
                            },
                            pattern_contracts: [
                                Contract::Pure,
                            ],
                            pattern_variable_arena: Arena {
                                data: [
                                    PatternVariable::Atom(
                                        0,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `dp`,
                                        0,
                                    ),
                                ],
                            ],
                            pattern_variable_modifiers: ArenaMap {
                                data: [
                                    Pure,
                                ],
                            },
                        },
                        variable_region: VariableRegionData {
                            inherited_variable_arena: Arena {
                                data: [
                                    InheritedVariableEntry {
                                        modifier: Pure,
                                        kind: InheritedVariableKind::Parenate {
                                            ident: `cc`,
                                        },
                                    },
                                ],
                            },
                            current_variable_arena: Arena {
                                data: [
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            3,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    18,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `dp`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                ],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 0,
                            },
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 1,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 5,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 7,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 8,
                            },
                        ],
                        has_self_lifetime: false,
                        has_self_place: false,
                        pattern_to_current_variable_map: [
                            (
                                0,
                                0,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
    (
        ItemPath(`mnist_classifier::digits::one::downmost`),
        Some(
            ItemSynDefn {
                body: 10,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::one::downmost`, `Ritchie(
                                                    Fn,
                                                )`, (0)),
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 0,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Tilde,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                                opd: 0,
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::f32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Option,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    10,
                                                ),
                                                opd: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `ConcaveComponent`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `f32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            11,
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
                                    pattern_region: SynPatternRegion {
                                        pattern_arena: Arena {
                                            data: [
                                                SynPatternData::Ident {
                                                    symbol_modifier_tokens: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `cc`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            4,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_contracts: [
                                            Contract::Pure,
                                        ],
                                        pattern_variable_arena: Arena {
                                            data: [
                                                PatternVariable::Atom(
                                                    0,
                                                ),
                                            ],
                                        },
                                        pattern_variable_maps: [
                                            [
                                                (
                                                    `cc`,
                                                    0,
                                                ),
                                            ],
                                        ],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [
                                                Pure,
                                            ],
                                        },
                                    },
                                    variable_region: VariableRegionData {
                                        inherited_variable_arena: Arena {
                                            data: [],
                                        },
                                        current_variable_arena: Arena {
                                            data: [
                                                CurrentVariableEntry {
                                                    modifier: Pure,
                                                    access_start: RegionalTokenIdx(
                                                        5,
                                                    ),
                                                    access_end: None,
                                                    data: CurrentVariableData::SimpleParenateParameter {
                                                        ident: `cc`,
                                                        pattern_variable_idx: 0,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: False,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [
                                            (
                                                SimpleParenateParameter {
                                                    syn_pattern_root: ParenateParameterSynPatternRoot {
                                                        syn_pattern_idx: 0,
                                                    },
                                                    ty: 1,
                                                },
                                                ArenaIdxRange(
                                                    0..1,
                                                ),
                                            ),
                                        ],
                                    },
                                    pattern_roots: [
                                        SynPatternRoot {
                                            kind: SynPatternRootKind::Parenate,
                                            syn_pattern_idx: 0,
                                        },
                                    ],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ExplicitParameterType,
                                            syn_expr_idx: 1,
                                        },
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 3,
                                        },
                                    ],
                                    has_self_lifetime: false,
                                    has_self_place: false,
                                    pattern_to_current_variable_map: [
                                        (
                                            0,
                                            0,
                                        ),
                                    ],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::digits::one::downmost`, `Ritchie(
                                        Fn,
                                    )`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 2,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        11,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        14,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 3,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Leq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                    ropd: 4,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        16,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 6,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        17,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            18,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        20,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 7,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        21,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            22,
                                        ),
                                    },
                                },
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    opd: 8,
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        0..3,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 0,
                                            },
                                            variables: ArenaIdxRange(
                                                0..1,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                3,
                                            ),
                                        ),
                                    ),
                                    initial_value: 1,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            9,
                                        ),
                                    },
                                    condition: 5,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 9,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                            ],
                        },
                        pattern_region: SynPatternRegion {
                            pattern_arena: Arena {
                                data: [
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                2,
                                            ),
                                        },
                                    },
                                ],
                            },
                            pattern_contracts: [
                                Contract::Pure,
                            ],
                            pattern_variable_arena: Arena {
                                data: [
                                    PatternVariable::Atom(
                                        0,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `dp`,
                                        0,
                                    ),
                                ],
                            ],
                            pattern_variable_modifiers: ArenaMap {
                                data: [
                                    Pure,
                                ],
                            },
                        },
                        variable_region: VariableRegionData {
                            inherited_variable_arena: Arena {
                                data: [
                                    InheritedVariableEntry {
                                        modifier: Pure,
                                        kind: InheritedVariableKind::Parenate {
                                            ident: `cc`,
                                        },
                                    },
                                ],
                            },
                            current_variable_arena: Arena {
                                data: [
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            3,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    23,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `dp`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                ],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 0,
                            },
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 1,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 5,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 9,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 10,
                            },
                        ],
                        has_self_lifetime: false,
                        has_self_place: false,
                        pattern_to_current_variable_map: [
                            (
                                0,
                                0,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
    (
        ItemPath(`mnist_classifier::digits::one::hat`),
        Some(
            ItemSynDefn {
                body: 16,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::one::hat`, `Ritchie(
                                                    Fn,
                                                )`, (0)),
                                            ),
                                        ),
                                    ),
                                    expr_arena: Arena {
                                        data: [
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 0,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Tilde,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    6,
                                                ),
                                                opd: 0,
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::f32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::Prefix {
                                                opr: Option,
                                                opr_regional_token_idx: RegionalTokenIdx(
                                                    10,
                                                ),
                                                opd: 2,
                                            },
                                        ],
                                    },
                                    principal_item_path_expr_arena: Arena {
                                        data: [
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `ConcaveComponent`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `f32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            11,
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
                                    pattern_region: SynPatternRegion {
                                        pattern_arena: Arena {
                                            data: [
                                                SynPatternData::Ident {
                                                    symbol_modifier_tokens: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `cc`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            4,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_contracts: [
                                            Contract::Pure,
                                        ],
                                        pattern_variable_arena: Arena {
                                            data: [
                                                PatternVariable::Atom(
                                                    0,
                                                ),
                                            ],
                                        },
                                        pattern_variable_maps: [
                                            [
                                                (
                                                    `cc`,
                                                    0,
                                                ),
                                            ],
                                        ],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [
                                                Pure,
                                            ],
                                        },
                                    },
                                    variable_region: VariableRegionData {
                                        inherited_variable_arena: Arena {
                                            data: [],
                                        },
                                        current_variable_arena: Arena {
                                            data: [
                                                CurrentVariableEntry {
                                                    modifier: Pure,
                                                    access_start: RegionalTokenIdx(
                                                        5,
                                                    ),
                                                    access_end: None,
                                                    data: CurrentVariableData::SimpleParenateParameter {
                                                        ident: `cc`,
                                                        pattern_variable_idx: 0,
                                                    },
                                                },
                                            ],
                                        },
                                        allow_self_type: False,
                                        allow_self_value: False,
                                        pattern_ty_constraints: [
                                            (
                                                SimpleParenateParameter {
                                                    syn_pattern_root: ParenateParameterSynPatternRoot {
                                                        syn_pattern_idx: 0,
                                                    },
                                                    ty: 1,
                                                },
                                                ArenaIdxRange(
                                                    0..1,
                                                ),
                                            ),
                                        ],
                                    },
                                    pattern_roots: [
                                        SynPatternRoot {
                                            kind: SynPatternRootKind::Parenate,
                                            syn_pattern_idx: 0,
                                        },
                                    ],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ExplicitParameterType,
                                            syn_expr_idx: 1,
                                        },
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 3,
                                        },
                                    ],
                                    has_self_lifetime: false,
                                    has_self_place: false,
                                    pattern_to_current_variable_map: [
                                        (
                                            0,
                                            0,
                                        ),
                                    ],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::digits::one::hat`, `Ritchie(
                                        Fn,
                                    )`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 2,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        11,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        14,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 3,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                    ropd: 4,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        16,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 6,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        17,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `x`,
                                        regional_token_idx: RegionalTokenIdx(
                                            18,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        20,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 7,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    ropd: 8,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        22,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 10,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        23,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `y`,
                                        regional_token_idx: RegionalTokenIdx(
                                            24,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `dp`,
                                    regional_token_idx: RegionalTokenIdx(
                                        26,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        21,
                                    ),
                                    opd: 11,
                                },
                                SynExprData::Field {
                                    owner: 12,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `x`,
                                        regional_token_idx: RegionalTokenIdx(
                                            28,
                                        ),
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 13,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        25,
                                    ),
                                    ropd: 14,
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        0..4,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 0,
                                            },
                                            variables: ArenaIdxRange(
                                                0..1,
                                            ),
                                            colon_token: Ok(
                                                None,
                                            ),
                                            ty: None,
                                        },
                                    ),
                                    assign_token: Ok(
                                        EqRegionalToken(
                                            RegionalTokenIdx(
                                                3,
                                            ),
                                        ),
                                    ),
                                    initial_value: 1,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            9,
                                        ),
                                    },
                                    condition: 5,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            15,
                                        ),
                                    },
                                    condition: 9,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 15,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                            ],
                        },
                        pattern_region: SynPatternRegion {
                            pattern_arena: Arena {
                                data: [
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `dp`,
                                            regional_token_idx: RegionalTokenIdx(
                                                2,
                                            ),
                                        },
                                    },
                                ],
                            },
                            pattern_contracts: [
                                Contract::Pure,
                            ],
                            pattern_variable_arena: Arena {
                                data: [
                                    PatternVariable::Atom(
                                        0,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `dp`,
                                        0,
                                    ),
                                ],
                            ],
                            pattern_variable_modifiers: ArenaMap {
                                data: [
                                    Pure,
                                ],
                            },
                        },
                        variable_region: VariableRegionData {
                            inherited_variable_arena: Arena {
                                data: [
                                    InheritedVariableEntry {
                                        modifier: Pure,
                                        kind: InheritedVariableKind::Parenate {
                                            ident: `cc`,
                                        },
                                    },
                                ],
                            },
                            current_variable_arena: Arena {
                                data: [
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            3,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    29,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `dp`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                ],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 0,
                            },
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 1,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 5,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 9,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 15,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 16,
                            },
                        ],
                        has_self_lifetime: false,
                        has_self_place: false,
                        pattern_to_current_variable_map: [
                            (
                                0,
                                0,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
]
```