```rust
[
    (
        ItemPath(`mnist_classifier::line_segment_sketch::convexity::is_convex`),
        Some(
            ItemSynDefn {
                body: 93,
                syn_expr_region: SynExprRegion {
                    data: SynExprRegionData {
                        parent: Some(
                            SynExprRegion {
                                data: SynExprRegionData {
                                    parent: None,
                                    path: SynNodeRegionPath::ItemDecl(
                                        ItemSynNodePath::MajorItem(
                                            MajorItemSynNodePath::Form(
                                                MajorFormSynNodePath(`mnist_classifier::line_segment_sketch::convexity::is_convex`, `Ritchie(
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
                                                            TypePath(`mnist_classifier::line_segment_sketch::LineSegmentSketch`, `Struct`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 1,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::num::i32`, `Extern`),
                                                        ),
                                                    ),
                                                ),
                                            },
                                            SynExprData::PrincipalEntityPath {
                                                path_expr_idx: 2,
                                                opt_path: Some(
                                                    PrincipalEntityPath::MajorItem(
                                                        MajorItemPath::Type(
                                                            TypePath(`core::basic::bool`, `Extern`),
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
                                                        ident: `LineSegmentSketch`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            7,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`mnist_classifier::line_segment_sketch::LineSegmentSketch`, `Struct`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `i32`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            11,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::num::i32`, `Extern`),
                                                    ),
                                                ),
                                            },
                                            SynPrincipalEntityPathExpr::Root {
                                                path_name_token: PathNameRegionalToken::Ident(
                                                    IdentRegionalToken {
                                                        ident: `bool`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            14,
                                                        ),
                                                    },
                                                ),
                                                principal_entity_path: PrincipalEntityPath::MajorItem(
                                                    MajorItemPath::Type(
                                                        TypePath(`core::basic::bool`, `Extern`),
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
                                                        ident: `line_segment_sketch`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            5,
                                                        ),
                                                    },
                                                },
                                                SynPatternData::Ident {
                                                    symbol_modifier_tokens: None,
                                                    ident_token: IdentRegionalToken {
                                                        ident: `index`,
                                                        regional_token_idx: RegionalTokenIdx(
                                                            9,
                                                        ),
                                                    },
                                                },
                                            ],
                                        },
                                        pattern_contracts: [
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
                                            ],
                                        },
                                        pattern_variable_maps: [
                                            [
                                                (
                                                    `line_segment_sketch`,
                                                    0,
                                                ),
                                            ],
                                            [
                                                (
                                                    `index`,
                                                    1,
                                                ),
                                            ],
                                        ],
                                        pattern_variable_modifiers: ArenaMap {
                                            data: [
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
                                                        6,
                                                    ),
                                                    access_end: None,
                                                    data: CurrentVariableData::SimpleParenateParameter {
                                                        ident: `line_segment_sketch`,
                                                        pattern_variable_idx: 0,
                                                    },
                                                },
                                                CurrentVariableEntry {
                                                    modifier: Pure,
                                                    access_start: RegionalTokenIdx(
                                                        10,
                                                    ),
                                                    access_end: None,
                                                    data: CurrentVariableData::SimpleParenateParameter {
                                                        ident: `index`,
                                                        pattern_variable_idx: 1,
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
                                                    ty: 0,
                                                },
                                                ArenaIdxRange(
                                                    0..1,
                                                ),
                                            ),
                                            (
                                                SimpleParenateParameter {
                                                    syn_pattern_root: ParenateParameterSynPatternRoot {
                                                        syn_pattern_idx: 1,
                                                    },
                                                    ty: 1,
                                                },
                                                ArenaIdxRange(
                                                    1..2,
                                                ),
                                            ),
                                        ],
                                    },
                                    pattern_roots: [
                                        SynPatternRoot {
                                            kind: SynPatternRootKind::Parenate,
                                            syn_pattern_idx: 0,
                                        },
                                        SynPatternRoot {
                                            kind: SynPatternRootKind::Parenate,
                                            syn_pattern_idx: 1,
                                        },
                                    ],
                                    expr_roots: [
                                        SynExprRoot {
                                            kind: SynExprRootKind::ExplicitParameterType,
                                            syn_expr_idx: 0,
                                        },
                                        SynExprRoot {
                                            kind: SynExprRootKind::ExplicitParameterType,
                                            syn_expr_idx: 1,
                                        },
                                        SynExprRoot {
                                            kind: SynExprRootKind::ReturnType,
                                            syn_expr_idx: 2,
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
                                    ],
                                },
                            },
                        ),
                        path: SynNodeRegionPath::ItemDefn(
                            ItemSynNodePath::MajorItem(
                                MajorItemSynNodePath::Form(
                                    MajorFormSynNodePath(`mnist_classifier::line_segment_sketch::convexity::is_convex`, `Ritchie(
                                        Fn,
                                    )`, (0)),
                                ),
                            ),
                        ),
                        expr_arena: Arena {
                            data: [
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 0,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 1,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            8,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        9,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        14,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 3,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            16,
                                        ),
                                    },
                                },
                                SynExprData::InheritedVariable {
                                    ident: `index`,
                                    regional_token_idx: RegionalTokenIdx(
                                        18,
                                    ),
                                    inherited_variable_idx: 1,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `index`,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `L`,
                                    regional_token_idx: RegionalTokenIdx(
                                        20,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 5,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::RemEuclid,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    ropd: 6,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 4,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        17,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 7,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        21,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 8,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        22,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            23,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        24,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        25,
                                    ),
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        29,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 10,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        30,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            31,
                                        ),
                                    },
                                },
                                SynExprData::InheritedVariable {
                                    ident: `index`,
                                    regional_token_idx: RegionalTokenIdx(
                                        34,
                                    ),
                                    inherited_variable_idx: 1,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `index`,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        36,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 12,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        35,
                                    ),
                                    ropd: 13,
                                },
                                SynExprData::Delimitered {
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        33,
                                    ),
                                    item: 14,
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        37,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `L`,
                                    regional_token_idx: RegionalTokenIdx(
                                        39,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 15,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::RemEuclid,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        38,
                                    ),
                                    ropd: 16,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 11,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        32,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 17,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        40,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 18,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        41,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            42,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        43,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        44,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        48,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        52,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 20,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        49,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `rotation_direction_to`,
                                        regional_token_idx: RegionalTokenIdx(
                                            50,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        51,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 21,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        53,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `is_rotation_counterclockwise_result`,
                                    regional_token_idx: RegionalTokenIdx(
                                        55,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        57,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 23,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Eq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        56,
                                    ),
                                    ropd: 24,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        64,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 11,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        63,
                                    ),
                                    opd: 26,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        68,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 28,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        69,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            70,
                                        ),
                                    },
                                },
                                SynExprData::InheritedVariable {
                                    ident: `index`,
                                    regional_token_idx: RegionalTokenIdx(
                                        73,
                                    ),
                                    inherited_variable_idx: 1,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `index`,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        75,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 30,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::Sub,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        74,
                                    ),
                                    ropd: 31,
                                },
                                SynExprData::Delimitered {
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        72,
                                    ),
                                    item: 32,
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        76,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `L`,
                                    regional_token_idx: RegionalTokenIdx(
                                        78,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 33,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::RemEuclid,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        77,
                                    ),
                                    ropd: 34,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 29,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        71,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 35,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        79,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 36,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        80,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `points`,
                                        regional_token_idx: RegionalTokenIdx(
                                            81,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        83,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 38,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        84,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            85,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        86,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        87,
                                    ),
                                },
                                SynExprData::FrameVarDecl {
                                    regional_token_idx: RegionalTokenIdx(
                                        89,
                                    ),
                                    ident: `i1`,
                                    for_loop_varible_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        40,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        91,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 39,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Leq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        88,
                                    ),
                                    ropd: 40,
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 41,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        92,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            93,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        94,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        95,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 42,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        90,
                                    ),
                                    ropd: 43,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        100,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 45,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        101,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `contour`,
                                        regional_token_idx: RegionalTokenIdx(
                                            102,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        106,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 47,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        107,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            108,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        109,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        110,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `i1`,
                                    regional_token_idx: RegionalTokenIdx(
                                        112,
                                    ),
                                    current_variable_idx: 6,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        40,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 46,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        103,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            104,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        105,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 48,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    111,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 49,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        113,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        116,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 4,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        120,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        124,
                                    ),
                                    current_variable_idx: 7,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 6,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 52,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        121,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `cross`,
                                        regional_token_idx: RegionalTokenIdx(
                                            122,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        123,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 53,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        125,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        114,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 4,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 51,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        117,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max`,
                                        regional_token_idx: RegionalTokenIdx(
                                            118,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        119,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 54,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        126,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 55,
                                    opr: SynBinaryOpr::AssignOrDefEq,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        115,
                                    ),
                                    ropd: 56,
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        132,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 11,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                SynExprData::Prefix {
                                    opr: Minus,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        131,
                                    ),
                                    opd: 58,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        136,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 60,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        137,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            138,
                                        ),
                                    },
                                },
                                SynExprData::InheritedVariable {
                                    ident: `index`,
                                    regional_token_idx: RegionalTokenIdx(
                                        140,
                                    ),
                                    inherited_variable_idx: 1,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `index`,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `L`,
                                    regional_token_idx: RegionalTokenIdx(
                                        142,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 62,
                                    opr: SynBinaryOpr::Closed(
                                        BinaryClosedOpr::RemEuclid,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        141,
                                    ),
                                    ropd: 63,
                                },
                                SynExprData::IndexOrCompositionWithList {
                                    owner: 61,
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        139,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 64,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        143,
                                    ),
                                },
                                SynExprData::Field {
                                    owner: 65,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        144,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `points`,
                                        regional_token_idx: RegionalTokenIdx(
                                            145,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        147,
                                    ),
                                    current_variable_idx: 9,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 8,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 67,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        148,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            149,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        150,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        151,
                                    ),
                                },
                                SynExprData::FrameVarDecl {
                                    regional_token_idx: RegionalTokenIdx(
                                        153,
                                    ),
                                    ident: `i2`,
                                    for_loop_varible_idx: 10,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        69,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        155,
                                    ),
                                    current_variable_idx: 9,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 8,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 68,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Leq,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        152,
                                    ),
                                    ropd: 69,
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 70,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        156,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            157,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        158,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        159,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 71,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        154,
                                    ),
                                    ropd: 72,
                                },
                                SynExprData::InheritedVariable {
                                    ident: `line_segment_sketch`,
                                    regional_token_idx: RegionalTokenIdx(
                                        164,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `line_segment_sketch`,
                                    },
                                },
                                SynExprData::Field {
                                    owner: 74,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        165,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `contour`,
                                        regional_token_idx: RegionalTokenIdx(
                                            166,
                                        ),
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_interval`,
                                    regional_token_idx: RegionalTokenIdx(
                                        170,
                                    ),
                                    current_variable_idx: 5,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 5,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 76,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        171,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            172,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        173,
                                    ),
                                    items: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        174,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `i2`,
                                    regional_token_idx: RegionalTokenIdx(
                                        176,
                                    ),
                                    current_variable_idx: 10,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        69,
                                    ),
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 75,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        167,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `displacement`,
                                        regional_token_idx: RegionalTokenIdx(
                                            168,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        169,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 77,
                                            comma_regional_token_idx: Some(
                                                RegionalTokenIdx(
                                                    175,
                                                ),
                                            ),
                                        },
                                        SynCommaListItem {
                                            syn_expr_idx: 78,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        177,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        180,
                                    ),
                                    current_variable_idx: 8,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        184,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `displacement`,
                                    regional_token_idx: RegionalTokenIdx(
                                        188,
                                    ),
                                    current_variable_idx: 11,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 9,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 81,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        185,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `cross`,
                                        regional_token_idx: RegionalTokenIdx(
                                            186,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        187,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 82,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        189,
                                    ),
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        178,
                                    ),
                                    current_variable_idx: 8,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::MethodApplicationOrCall {
                                    self_argument: 80,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        181,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `max`,
                                        regional_token_idx: RegionalTokenIdx(
                                            182,
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        183,
                                    ),
                                    items: [
                                        SynCommaListItem {
                                            syn_expr_idx: 83,
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        190,
                                    ),
                                },
                                SynExprData::Binary {
                                    lopd: 84,
                                    opr: SynBinaryOpr::AssignOrDefEq,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        179,
                                    ),
                                    ropd: 85,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `current_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        192,
                                    ),
                                    current_variable_idx: 8,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 7,
                                    },
                                },
                                SynExprData::CurrentVariable {
                                    ident: `previous_raw_cross`,
                                    regional_token_idx: RegionalTokenIdx(
                                        194,
                                    ),
                                    current_variable_idx: 4,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 4,
                                    },
                                },
                                SynExprData::Binary {
                                    lopd: 87,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Less,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        193,
                                    ),
                                    ropd: 88,
                                },
                                SynExprData::CurrentVariable {
                                    ident: `is_rotation_counterclockwise_result`,
                                    regional_token_idx: RegionalTokenIdx(
                                        198,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 3,
                                    },
                                },
                                SynExprData::Literal(
                                    RegionalTokenIdx(
                                        200,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                                SynExprData::Binary {
                                    lopd: 90,
                                    opr: SynBinaryOpr::Comparison(
                                        BinaryComparisonOpr::Greater,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        199,
                                    ),
                                    ropd: 91,
                                },
                                SynExprData::Block {
                                    stmts: ArenaIdxRange(
                                        12..17,
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
                                            97,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 6,
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
                                                99,
                                            ),
                                        ),
                                    ),
                                    initial_value: 50,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 57,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            161,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 9,
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
                                                163,
                                            ),
                                        ),
                                    ),
                                    initial_value: 79,
                                },
                                SynStmtData::Eval {
                                    expr_idx: 86,
                                    eol_semicolon: Ok(
                                        None,
                                    ),
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            59,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 4,
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
                                                62,
                                            ),
                                        ),
                                    ),
                                    initial_value: 27,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            65,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 5,
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
                                                67,
                                            ),
                                        ),
                                    ),
                                    initial_value: 37,
                                },
                                SynStmtData::ForBetween {
                                    for_token: StmtForRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            82,
                                        ),
                                    },
                                    particulars: SynForBetweenParticulars {
                                        for_between_loop_var_regional_token_idx: RegionalTokenIdx(
                                            89,
                                        ),
                                        for_between_loop_var_ident: `i1`,
                                        for_between_loop_var_expr_idx: 40,
                                        range: Ok(
                                            SynForBetweenRange {
                                                initial_boundary: SynForBetweenLoopBoundary {
                                                    bound_expr: Some(
                                                        39,
                                                    ),
                                                    kind: LowerClosed,
                                                },
                                                final_boundary: SynForBetweenLoopBoundary {
                                                    bound_expr: Some(
                                                        43,
                                                    ),
                                                    kind: UpperOpen,
                                                },
                                                step: Constant(
                                                    1,
                                                ),
                                            },
                                        ),
                                    },
                                    for_loop_varible_idx: 6,
                                    eol_colon: Ok(
                                        EolRegionalToken::Colon(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    96,
                                                ),
                                            },
                                        ),
                                    ),
                                    block: ArenaIdxRange(
                                        0..2,
                                    ),
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            127,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 7,
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
                                                130,
                                            ),
                                        ),
                                    ),
                                    initial_value: 59,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            133,
                                        ),
                                    },
                                    let_variables_pattern: Ok(
                                        LetPatternSyndicate {
                                            syn_pattern_root: LetPatternSynExprRoot {
                                                syn_pattern_idx: 8,
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
                                                135,
                                            ),
                                        ),
                                    ),
                                    initial_value: 66,
                                },
                                SynStmtData::ForBetween {
                                    for_token: StmtForRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            146,
                                        ),
                                    },
                                    particulars: SynForBetweenParticulars {
                                        for_between_loop_var_regional_token_idx: RegionalTokenIdx(
                                            153,
                                        ),
                                        for_between_loop_var_ident: `i2`,
                                        for_between_loop_var_expr_idx: 69,
                                        range: Ok(
                                            SynForBetweenRange {
                                                initial_boundary: SynForBetweenLoopBoundary {
                                                    bound_expr: Some(
                                                        68,
                                                    ),
                                                    kind: LowerClosed,
                                                },
                                                final_boundary: SynForBetweenLoopBoundary {
                                                    bound_expr: Some(
                                                        72,
                                                    ),
                                                    kind: UpperOpen,
                                                },
                                                step: Constant(
                                                    1,
                                                ),
                                            },
                                        ),
                                    },
                                    for_loop_varible_idx: 10,
                                    eol_colon: Ok(
                                        EolRegionalToken::Colon(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    160,
                                                ),
                                            },
                                        ),
                                    ),
                                    block: ArenaIdxRange(
                                        2..4,
                                    ),
                                },
                                SynStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            191,
                                        ),
                                    },
                                    result: 89,
                                },
                                SynStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            197,
                                        ),
                                    },
                                    result: 92,
                                },
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
                                    initial_value: 2,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            11,
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
                                                13,
                                            ),
                                        ),
                                    ),
                                    initial_value: 9,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            26,
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
                                                28,
                                            ),
                                        ),
                                    ),
                                    initial_value: 19,
                                },
                                SynStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            45,
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
                                                47,
                                            ),
                                        ),
                                    ),
                                    initial_value: 22,
                                },
                                SynStmtData::IfElse {
                                    if_branch: SynIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                54,
                                            ),
                                        },
                                        condition: Ok(
                                            25,
                                        ),
                                        eol_colon: Ok(
                                            EolColonRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    58,
                                                ),
                                            },
                                        ),
                                        stmts: ArenaIdxRange(
                                            4..11,
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: Some(
                                        SynElseBranch {
                                            else_token: ElseRegionalToken {
                                                regional_token_idx: RegionalTokenIdx(
                                                    195,
                                                ),
                                            },
                                            eol_colon_token: Ok(
                                                EolColonRegionalToken {
                                                    regional_token_idx: RegionalTokenIdx(
                                                        196,
                                                    ),
                                                },
                                            ),
                                            stmts: ArenaIdxRange(
                                                11..12,
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
                                            ident: `L`,
                                            regional_token_idx: RegionalTokenIdx(
                                                2,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `current_displacement`,
                                            regional_token_idx: RegionalTokenIdx(
                                                12,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `previous_displacement`,
                                            regional_token_idx: RegionalTokenIdx(
                                                27,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `is_rotation_counterclockwise_result`,
                                            regional_token_idx: RegionalTokenIdx(
                                                46,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: Some(
                                            Mut(
                                                MutRegionalToken {
                                                    regional_token_idx: RegionalTokenIdx(
                                                        60,
                                                    ),
                                                },
                                            ),
                                        ),
                                        ident_token: IdentRegionalToken {
                                            ident: `previous_raw_cross`,
                                            regional_token_idx: RegionalTokenIdx(
                                                61,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `previous_interval`,
                                            regional_token_idx: RegionalTokenIdx(
                                                66,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `displacement`,
                                            regional_token_idx: RegionalTokenIdx(
                                                98,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: Some(
                                            Mut(
                                                MutRegionalToken {
                                                    regional_token_idx: RegionalTokenIdx(
                                                        128,
                                                    ),
                                                },
                                            ),
                                        ),
                                        ident_token: IdentRegionalToken {
                                            ident: `current_raw_cross`,
                                            regional_token_idx: RegionalTokenIdx(
                                                129,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `current_interval`,
                                            regional_token_idx: RegionalTokenIdx(
                                                134,
                                            ),
                                        },
                                    },
                                    SynPatternData::Ident {
                                        symbol_modifier_tokens: None,
                                        ident_token: IdentRegionalToken {
                                            ident: `displacement`,
                                            regional_token_idx: RegionalTokenIdx(
                                                162,
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
                                Contract::Move,
                                Contract::Pure,
                                Contract::Pure,
                                Contract::Move,
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
                                        4,
                                    ),
                                    PatternVariable::Atom(
                                        5,
                                    ),
                                    PatternVariable::Atom(
                                        6,
                                    ),
                                    PatternVariable::Atom(
                                        7,
                                    ),
                                    PatternVariable::Atom(
                                        8,
                                    ),
                                    PatternVariable::Atom(
                                        9,
                                    ),
                                ],
                            },
                            pattern_variable_maps: [
                                [
                                    (
                                        `L`,
                                        0,
                                    ),
                                ],
                                [
                                    (
                                        `current_displacement`,
                                        1,
                                    ),
                                ],
                                [
                                    (
                                        `previous_displacement`,
                                        2,
                                    ),
                                ],
                                [
                                    (
                                        `is_rotation_counterclockwise_result`,
                                        3,
                                    ),
                                ],
                                [
                                    (
                                        `previous_raw_cross`,
                                        4,
                                    ),
                                ],
                                [
                                    (
                                        `previous_interval`,
                                        5,
                                    ),
                                ],
                                [
                                    (
                                        `displacement`,
                                        6,
                                    ),
                                ],
                                [
                                    (
                                        `current_raw_cross`,
                                        7,
                                    ),
                                ],
                                [
                                    (
                                        `current_interval`,
                                        8,
                                    ),
                                ],
                                [
                                    (
                                        `displacement`,
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
                                    Mut,
                                    Pure,
                                    Pure,
                                    Mut,
                                    Pure,
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
                                            ident: `line_segment_sketch`,
                                        },
                                    },
                                    InheritedVariableEntry {
                                        modifier: Pure,
                                        kind: InheritedVariableKind::Parenate {
                                            ident: `index`,
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
                                                    201,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `L`,
                                            pattern_variable_idx: 0,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            13,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    201,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `current_displacement`,
                                            pattern_variable_idx: 1,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            28,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    201,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `previous_displacement`,
                                            pattern_variable_idx: 2,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            47,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    201,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `is_rotation_counterclockwise_result`,
                                            pattern_variable_idx: 3,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Mut,
                                        access_start: RegionalTokenIdx(
                                            62,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    195,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `previous_raw_cross`,
                                            pattern_variable_idx: 4,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            67,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    195,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `previous_interval`,
                                            pattern_variable_idx: 5,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            97,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    127,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LoopVariable {
                                            ident: `i1`,
                                            expr_idx: 40,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            99,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    127,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `displacement`,
                                            pattern_variable_idx: 6,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Mut,
                                        access_start: RegionalTokenIdx(
                                            130,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    195,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `current_raw_cross`,
                                            pattern_variable_idx: 7,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            135,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    195,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `current_interval`,
                                            pattern_variable_idx: 8,
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
                                                    191,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LoopVariable {
                                            ident: `i2`,
                                            expr_idx: 69,
                                        },
                                    },
                                    CurrentVariableEntry {
                                        modifier: Pure,
                                        access_start: RegionalTokenIdx(
                                            163,
                                        ),
                                        access_end: Some(
                                            RegionalTokenIdxRangeEnd(
                                                RegionalTokenIdx(
                                                    191,
                                                ),
                                            ),
                                        ),
                                        data: CurrentVariableData::LetVariable {
                                            ident: `displacement`,
                                            pattern_variable_idx: 9,
                                        },
                                    },
                                ],
                            },
                            allow_self_type: False,
                            allow_self_value: False,
                            pattern_ty_constraints: [
                                (
                                    LoopVariable,
                                    ArenaIdxRange(
                                        6..7,
                                    ),
                                ),
                                (
                                    LoopVariable,
                                    ArenaIdxRange(
                                        10..11,
                                    ),
                                ),
                            ],
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
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 4,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 5,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
                                syn_pattern_idx: 6,
                            },
                            SynPatternRoot {
                                kind: SynPatternRootKind::Let,
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
                        ],
                        expr_roots: [
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 2,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 9,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 19,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 22,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 27,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 37,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 50,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 57,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 59,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 66,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::LetStmtInitialValue,
                                syn_expr_idx: 79,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::EvalExpr,
                                syn_expr_idx: 86,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::ReturnExpr,
                                syn_expr_idx: 89,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::ReturnExpr,
                                syn_expr_idx: 92,
                            },
                            SynExprRoot {
                                kind: SynExprRootKind::RootBody,
                                syn_expr_idx: 93,
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
                                5,
                                5,
                            ),
                            (
                                6,
                                7,
                            ),
                            (
                                7,
                                8,
                            ),
                            (
                                8,
                                9,
                            ),
                            (
                                9,
                                11,
                            ),
                        ],
                    },
                },
            },
        ),
    ),
]
```