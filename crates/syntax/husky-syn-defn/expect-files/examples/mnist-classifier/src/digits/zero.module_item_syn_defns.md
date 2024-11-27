```rust
[
    (
        ItemPath(`mnist_classifier::digits::zero::open_one_match`),
        Some(
            ItemSynDefn {
                body: 5,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::zero::open_one_match`, `Val`, (0)),
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
                                    MajorFormSynNodePath(`mnist_classifier::digits::zero::open_one_match`, `Val`, (0)),
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
                                                MajorFormPath(`mnist_classifier::digits::zero::almost_closed`, `Ritchie(
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
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        7,
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
                                            syn_expr_idx: 3,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
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
                                            ident: `almost_closed`,
                                            regional_token_idx: RegionalTokenIdx(
                                                6,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::zero::almost_closed`, `Ritchie(
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
                                    expr_idx: 4,
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
                                syn_expr_idx: 4,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 5,
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
        ItemPath(`mnist_classifier::digits::zero::almost_closed`),
        Some(
            ItemSynDefn {
                body: 12,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::zero::almost_closed`, `Ritchie(
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
                                    MajorFormSynNodePath(`mnist_classifier::digits::zero::almost_closed`, `Ritchie(
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
                                        2,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        3,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change`,
                                        regional_token_idx: RegionalTokenIdx(
                                            4,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        6,
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
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        9,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 12,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 1,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Add,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ropd: 2,
                                },
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                    opd: 3,
                                },
                                SynExprData::Binary {
                                    lopd: 4,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    ropd: 5,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        11,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 7,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        12,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change`,
                                        regional_token_idx: RegionalTokenIdx(
                                            13,
                                        ),
                                    },
                                },
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    opd: 8,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        15,
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
                                    lopd: 9,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Add,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        14,
                                    ),
                                    ropd: 10,
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        0..2,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [],
                        },
                        stmt_arena: Arena {
                            data: [
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                    },
                                    condition: 6,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 11,
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
                                data: [],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [],
                        },
                        pattern_roots: [],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 6,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 11,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 12,
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
        ItemPath(`mnist_classifier::digits::zero::is_zero`),
        Some(
            ItemSynDefn {
                body: 90,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::digits::zero::is_zero`, `Val`, (0)),
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
                                                        TypeVariantPath(`mnist::MnistLabel::Zero`),
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
                                                            8,
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
                                                            9,
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
                                                            10,
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
                                                        11,
                                                    ),
                                                ),
                                                ident_token: Ok(
                                                    IdentRegionalToken {
                                                        ident: `Zero`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            12,
                                                        ),
                                                    },
                                                ),
                                                path: Ok(
                                                    PrincipalEntityPath::TypeVariant(
                                                        TypeVariantPath(`mnist::MnistLabel::Zero`),
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
                                    MajorFormSynNodePath(`mnist_classifier::digits::zero::is_zero`, `Val`, (0)),
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
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        3,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `raw_contours`,
                                        regional_token_idx: RegionalTokenIdx(
                                            4,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 1,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ilen`,
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
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        10,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 2,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        9,
                                    ),
                                    ropd: 3,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 5,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        16,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            17,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `n`,
                                    regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        21,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 13,
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
                                        20,
                                    ),
                                    ropd: 8,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 2,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 10,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        24,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            25,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        27,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 11,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        26,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 12,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        28,
                                    ),
                                },
                                SynExprData::Be {
                                    src: 13,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        29,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 2,
                                            },
                                            variables: ArenaIdxRange(
                                                1..1,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 4,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 15,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        36,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            37,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        38,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        39,
                                    ),
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        41,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 16,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        40,
                                    ),
                                    ropd: 17,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 5,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 19,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        46,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            47,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        49,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 20,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        48,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 21,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        50,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 22,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        51,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 23,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        52,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            53,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        54,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        55,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 24,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        56,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            57,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        58,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        59,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `c`,
                                    regional_token_idx: RegionalTokenIdx(
                                        61,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        63,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 14,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 26,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        62,
                                    ),
                                    ropd: 27,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 7,
                                    opt_path: Some(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 8,
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
                                    path_expr_idx: 9,
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
                                        75,
                                    ),
                                    items: [],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        76,
                                    ),
                                },
                                SynExprData::FunctionApplicationOrCall {
                                    function: 30,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        72,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 31,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    74,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 32,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        77,
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 10,
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
                                    ident: `simp_zero_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        80,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 35,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        81,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            82,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_zero_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        84,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 37,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        85,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rel_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            86,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_zero_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        88,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 39,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        89,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `angle_change_norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            90,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        94,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            5,
                                        ),
                                    ),
                                ),
                                SynExprData::FunctionCall {
                                    function: 34,
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        79,
                                    ),
                                    items: [
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 36,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        83,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 38,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        87,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::SimpleOrVariadic(
                                            SynSimpleOrVariadicCallListItem {
                                                argument_expr_idx: 40,
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        91,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SynCallListItem::Keyed(
                                            SynKeyedCallListItem {
                                                key_regional_token_idx: RegionalTokenIdx(
                                                    92,
                                                ),
                                                key: `skip`,
                                                argument_expr_idx: 41,
                                                separator: CallListSeparator::None,
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        95,
                                    ),
                                },
                                SynExprData::Suffix {
                                    opd: 42,
                                    opr: UnveilOrComposeWithOption,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        96,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_zero_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        98,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 44,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        99,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            100,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        102,
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
                                    lopd: 45,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        101,
                                    ),
                                    ropd: 46,
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
                                    owner: 48,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        105,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `eff_holes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            106,
                                        ),
                                    },
                                },
                                SynExprData::Field {
                                    owner: 49,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        107,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            108,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        110,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 50,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        109,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 51,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        111,
                                    ),
                                },
                                SynExprData::Be {
                                    src: 52,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        112,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 5,
                                            },
                                            variables: ArenaIdxRange(
                                                3..3,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 13,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 54,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        116,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `eff_holes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            117,
                                        ),
                                    },
                                },
                                SynExprData::Field {
                                    owner: 55,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        118,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            119,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        121,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 56,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        120,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 57,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        122,
                                    ),
                                },
                                SynExprData::Be {
                                    src: 58,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        123,
                                    ),
                                    target: Ok(
                                        BePatternSyndicate {
                                            pattern_root: BeSynPatternRoot {
                                                syn_pattern_idx: 7,
                                            },
                                            variables: ArenaIdxRange(
                                                3..3,
                                            ),
                                        },
                                    ),
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 15,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 60,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        132,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `eff_holes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            133,
                                        ),
                                    },
                                },
                                SynExprData::Field {
                                    owner: 61,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        134,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            135,
                                        ),
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        137,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 62,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        136,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 63,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        138,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `major_hole`,
                                    regional_token_idx: RegionalTokenIdx(
                                        142,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 65,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        143,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 66,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        144,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            145,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `major_hole`,
                                    regional_token_idx: RegionalTokenIdx(
                                        151,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::Suffix {
                                    opd: 68,
                                    opr: UnwrapOrComposeWithNot,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        152,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 69,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        153,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            154,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 67,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        146,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymax`,
                                        regional_token_idx: RegionalTokenIdx(
                                            147,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        148,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        149,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 70,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        155,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymin`,
                                        regional_token_idx: RegionalTokenIdx(
                                            156,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        157,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        158,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 71,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        150,
                                    ),
                                    ropd: 72,
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 16,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 74,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        163,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            164,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 17,
                                    opt_path: Some(
                                        PrincipalEntityPath::MajorItem(
                                            MajorItemPath::Form(
                                                MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                            ),
                                        ),
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 76,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        171,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            172,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 75,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        165,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymax`,
                                        regional_token_idx: RegionalTokenIdx(
                                            166,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        167,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        168,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 77,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        173,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymin`,
                                        regional_token_idx: RegionalTokenIdx(
                                            174,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        175,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        176,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 78,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        169,
                                    ),
                                    ropd: 79,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `a`,
                                    regional_token_idx: RegionalTokenIdx(
                                        180,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 6,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `b`,
                                    regional_token_idx: RegionalTokenIdx(
                                        182,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 81,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Div,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        181,
                                    ),
                                    ropd: 82,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `ratio`,
                                    regional_token_idx: RegionalTokenIdx(
                                        184,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 8,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        186,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 16,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 84,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Greater,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        185,
                                    ),
                                    ropd: 85,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `simp_zero_match`,
                                    regional_token_idx: RegionalTokenIdx(
                                        190,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 87,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        191,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `norm`,
                                        regional_token_idx: RegionalTokenIdx(
                                            192,
                                        ),
                                    },
                                },
                                SynExprData::PrincipalEntityPath {
                                    path_expr_idx: 19,
                                    opt_path: Some(
                                        PrincipalEntityPath::TypeVariant(
                                            TypeVariantPath(`malamute::OneVsAll::Yes`),
                                        ),
                                    ),
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        7..20,
                                    ),
                                },
                            ],
                        },
                        principal_item_path_expr_arena: Arena {
                            data: [
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                2,
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
                                            ident: `open_one_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                15,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `open_one_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                23,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `Some`,
                                            regional_token_idx: RegionalTokenIdx(
                                                30,
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
                                            ident: `connected_components`,
                                            regional_token_idx: RegionalTokenIdx(
                                                35,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `open_one_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                45,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::zero::open_one_match`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `OneVsAll`,
                                            regional_token_idx: RegionalTokenIdx(
                                                65,
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
                                    parent: 6,
                                    colon_colon_token: ColonColonRegionalToken(
                                        RegionalTokenIdx(
                                            66,
                                        ),
                                    ),
                                    ident_token: Ok(
                                        IdentRegionalToken {
                                            ident: `Yes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                67,
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
                                            ident: `fermi_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                71,
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
                                                73,
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
                                                78,
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
                                                104,
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
                                            ident: `None`,
                                            regional_token_idx: RegionalTokenIdx(
                                                113,
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
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                115,
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
                                            ident: `Some`,
                                            regional_token_idx: RegionalTokenIdx(
                                                124,
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
                                            ident: `major_connected_component`,
                                            regional_token_idx: RegionalTokenIdx(
                                                131,
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
                                            ident: `major_line_segment_sketch`,
                                            regional_token_idx: RegionalTokenIdx(
                                                162,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `major_line_segment_sketch`,
                                            regional_token_idx: RegionalTokenIdx(
                                                170,
                                            ),
                                        },
                                    ),
                                    principal_entity_path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                        ),
                                    ),
                                },
                                SynPrincipalEntityPathExpr::Root {
                                    path_name_token: PathNameRegionalToken::Ident(
                                        IdentRegionalToken {
                                            ident: `OneVsAll`,
                                            regional_token_idx: RegionalTokenIdx(
                                                193,
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
                                    parent: 18,
                                    colon_colon_token: ColonColonRegionalToken(
                                        RegionalTokenIdx(
                                            194,
                                        ),
                                    ),
                                    ident_token: Ok(
                                        IdentRegionalToken {
                                            ident: `Yes`,
                                            regional_token_idx: RegionalTokenIdx(
                                                195,
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
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
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
                                                14,
                                            ),
                                        ),
                                    ),
                                    initial_value: 6,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            18,
                                        ),
                                    },
                                    condition: 9,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            22,
                                        ),
                                    },
                                    condition: 14,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            34,
                                        ),
                                    },
                                    condition: 18,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            42,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 3,
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
                                                44,
                                            ),
                                        ),
                                    ),
                                    initial_value: 25,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            60,
                                        ),
                                    },
                                    condition: 28,
                                },
                                SynStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            64,
                                        ),
                                    },
                                    result: 29,
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                1,
                                            ),
                                        },
                                        condition: Ok(
                                            4,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    11,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            0..7,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            68,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 4,
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
                                                70,
                                            ),
                                        ),
                                    ),
                                    initial_value: 33,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 43,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            97,
                                        ),
                                    },
                                    condition: 47,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            103,
                                        ),
                                    },
                                    condition: 53,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            114,
                                        ),
                                    },
                                    condition: 59,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            128,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 8,
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
                                                130,
                                            ),
                                        ),
                                    ),
                                    initial_value: 64,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            139,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 9,
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
                                                141,
                                            ),
                                        ),
                                    ),
                                    initial_value: 73,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            159,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 10,
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
                                                161,
                                            ),
                                        ),
                                    ),
                                    initial_value: 80,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            177,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 11,
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
                                                179,
                                            ),
                                        ),
                                    ),
                                    initial_value: 83,
                                },
                                SynStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            183,
                                        ),
                                    },
                                    condition: 86,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            187,
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
                                                189,
                                            ),
                                        ),
                                    ),
                                    initial_value: 88,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 89,
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
                                            ident: `n`,
                                            regional_token_idx: RegionalTokenIdx(
                                                13,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `_`,
                                            regional_token_idx: RegionalTokenIdx(
                                                32,
                                            ),
                                        },
                                    },
                                    SynPatternData::TupleTypeVariant {
                                        path_expr_idx: 3,
                                        path: TypeVariantPath(`core::option::Option::Some`),
                                        lpar: LparRegionalToken(
                                            RegionalTokenIdx(
                                                31,
                                            ),
                                        ),
                                        fields: PunctuatedSmallList {
                                            elements: [
                                                SynPatternComponent(
                                                    1,
                                                ),
                                            ],
                                            separators: [],
                                            phantom: PhantomData<husky_syn_expr::error::SynExprError>,
                                        },
                                        rpar: RparRegionalToken(
                                            RegionalTokenIdx(
                                                33,
                                            ),
                                        ),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `c`,
                                            regional_token_idx: RegionalTokenIdx(
                                                43,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `simp_zero_match`,
                                            regional_token_idx: RegionalTokenIdx(
                                                69,
                                            ),
                                        },
                                    },
                                    SynPatternData::UnitTypeVariant {
                                        path_expr_idx: 12,
                                        path: TypeVariantPath(`core::option::Option::None`),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `_`,
                                            regional_token_idx: RegionalTokenIdx(
                                                126,
                                            ),
                                        },
                                    },
                                    SynPatternData::TupleTypeVariant {
                                        path_expr_idx: 14,
                                        path: TypeVariantPath(`core::option::Option::Some`),
                                        lpar: LparRegionalToken(
                                            RegionalTokenIdx(
                                                125,
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
                                                127,
                                            ),
                                        ),
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `major_hole`,
                                            regional_token_idx: RegionalTokenIdx(
                                                129,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `a`,
                                            regional_token_idx: RegionalTokenIdx(
                                                140,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `b`,
                                            regional_token_idx: RegionalTokenIdx(
                                                160,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `ratio`,
                                            regional_token_idx: RegionalTokenIdx(
                                                178,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `a`,
                                            regional_token_idx: RegionalTokenIdx(
                                                188,
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
                                        3,
                                    ),
                                    PatternVariable::Atom(
                                        4,
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
                                        11,
                                    ),
                                    PatternVariable::Atom(
                                        12,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `n`,
                                        0,
                                    ),
                                ],
                                [
                                    (
                                        `_`,
                                        1,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `c`,
                                        2,
                                    ),
                                ],
                                [
                                    (
                                        `simp_zero_match`,
                                        3,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `_`,
                                        4,
                                    ),
                                ],
                                [],
                                [
                                    (
                                        `major_hole`,
                                        5,
                                    ),
                                ],
                                [
                                    (
                                        `a`,
                                        6,
                                    ),
                                ],
                                [
                                    (
                                        `b`,
                                        7,
                                    ),
                                ],
                                [
                                    (
                                        `ratio`,
                                        8,
                                    ),
                                ],
                                [
                                    (
                                        `a`,
                                        9,
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
                                            14,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    68,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `n`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            44,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    68,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `c`,
                                            pattern_variable_idx: 2,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            70,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `simp_zero_match`,
                                            pattern_variable_idx: 3,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            130,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `major_hole`,
                                            pattern_variable_idx: 5,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            141,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `a`,
                                            pattern_variable_idx: 6,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            161,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `b`,
                                            pattern_variable_idx: 7,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            179,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `ratio`,
                                            pattern_variable_idx: 8,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            189,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    196,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `a`,
                                            pattern_variable_idx: 9,
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
                                kind: SynPatternRootKind::Be,
                                syn_pattern_idx: 2,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 3,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 4,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Be,
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
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 10,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 11,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 12,
                            },
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 6,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 9,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 14,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 18,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 25,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 28,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::ReturnExpr,
                                syn_expr_idx: 29,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 33,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 43,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 47,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 53,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 59,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 64,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 73,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 80,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 83,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::Condition,
                                syn_expr_idx: 86,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 88,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 89,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 90,
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
                                2,
                                1,
                            ),
                            (
                                3,
                                2,
                            ),
                            (
                                5,
                                3,
                            ),
                            (
                                6,
                                4,
                            ),
                            (
                                7,
                                5,
                            ),
                            (
                                8,
                                6,
                            ),
                            (
                                9,
                                7,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
]
```