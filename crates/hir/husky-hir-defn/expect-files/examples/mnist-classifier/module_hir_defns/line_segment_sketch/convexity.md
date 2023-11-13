[
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::FunctionFn(
                FunctionFnFugitiveHirDefn {
                    path: FugitivePath(`mnist_classifier::line_segment_sketch::convexity::is_convex`, `FunctionFn`),
                    hir_decl: FunctionFnFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::line_segment_sketch::convexity::is_convex`, `FunctionFn`),
                        template_parameters: HirTemplateParameters(
                            [],
                        ),
                        parenate_parameters: HirEagerParenateParameters(
                            [
                                Ordinary {
                                    pattern_expr_idx: 1,
                                    ty: PathLeading(
                                        HirTypePathLeading(
                                            Id {
                                                value: 58,
                                            },
                                        ),
                                    ),
                                },
                                Ordinary {
                                    pattern_expr_idx: 2,
                                    ty: PathLeading(
                                        HirTypePathLeading(
                                            Id {
                                                value: 5,
                                            },
                                        ),
                                    ),
                                },
                            ],
                        ),
                        return_ty: HirType::PathLeading(
                            HirTypePathLeading {
                                ty_path: TypePath(`core::basic::bool`, `Extern`),
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
                                        symbol_modifier: None,
                                        ident: Ident(
                                            Coword(
                                                Id {
                                                    value: 220,
                                                },
                                            ),
                                        ),
                                    },
                                    Ident {
                                        symbol_modifier: None,
                                        ident: Ident(
                                            Coword(
                                                Id {
                                                    value: 421,
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
                                                            value: 220,
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
                                                            value: 421,
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
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            86,
                            HirEagerExprRegion {
                                hir_eager_expr_arena: Arena {
                                    data: [
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 1,
                                            ident: `strokes`,
                                        },
                                        HirEagerExprData::MethodCall {
                                            self_argument: 2,
                                            ident: `ilen`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 4,
                                            ident: `strokes`,
                                        },
                                        HirEagerExprData::Variable(
                                            2,
                                        ),
                                        HirEagerExprData::Variable(
                                            3,
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 6,
                                            opr: Closed(
                                                RemEuclid,
                                            ),
                                            ropd: 7,
                                        },
                                        HirEagerExprData::Index {
                                            owner_hir_expr_idx: 5,
                                            items: [
                                                8,
                                            ],
                                        },
                                        HirEagerExprData::MethodCall {
                                            self_argument: 9,
                                            ident: `displacement`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 11,
                                            ident: `strokes`,
                                        },
                                        HirEagerExprData::Variable(
                                            2,
                                        ),
                                        HirEagerExprData::Literal(
                                            TermLiteral::I32(
                                                1,
                                            ),
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 13,
                                            opr: Closed(
                                                Sub,
                                            ),
                                            ropd: 14,
                                        },
                                        HirEagerExprData::Variable(
                                            3,
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 15,
                                            opr: Closed(
                                                RemEuclid,
                                            ),
                                            ropd: 16,
                                        },
                                        HirEagerExprData::Index {
                                            owner_hir_expr_idx: 12,
                                            items: [
                                                17,
                                            ],
                                        },
                                        HirEagerExprData::MethodCall {
                                            self_argument: 18,
                                            ident: `displacement`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            5,
                                        ),
                                        HirEagerExprData::Variable(
                                            4,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 20,
                                            ident: `rotation_direction_to`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    21,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::Variable(
                                            6,
                                        ),
                                        HirEagerExprData::Literal(
                                            TermLiteral::I32(
                                                0,
                                            ),
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 23,
                                            opr: Comparison(
                                                Eq,
                                            ),
                                            ropd: 24,
                                        },
                                        HirEagerExprData::Literal(
                                            TermLiteral::F32(
                                                NotNan(
                                                    999999.0,
                                                ),
                                            ),
                                        ),
                                        HirEagerExprData::Prefix {
                                            opr: Minus,
                                            opd_hir_expr_idx: 26,
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 28,
                                            ident: `strokes`,
                                        },
                                        HirEagerExprData::Variable(
                                            2,
                                        ),
                                        HirEagerExprData::Literal(
                                            TermLiteral::I32(
                                                1,
                                            ),
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 30,
                                            opr: Closed(
                                                Sub,
                                            ),
                                            ropd: 31,
                                        },
                                        HirEagerExprData::Variable(
                                            3,
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 32,
                                            opr: Closed(
                                                RemEuclid,
                                            ),
                                            ropd: 33,
                                        },
                                        HirEagerExprData::Index {
                                            owner_hir_expr_idx: 29,
                                            items: [
                                                34,
                                            ],
                                        },
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 35,
                                            ident: `points`,
                                        },
                                        HirEagerExprData::Variable(
                                            8,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 37,
                                            ident: `start`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            8,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 39,
                                            ident: `end`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 41,
                                            ident: `contour`,
                                        },
                                        HirEagerExprData::Variable(
                                            8,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 43,
                                            ident: `start`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            9,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 42,
                                            ident: `displacement`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    44,
                                                ),
                                                Regular(
                                                    45,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::Variable(
                                            7,
                                        ),
                                        HirEagerExprData::Variable(
                                            7,
                                        ),
                                        HirEagerExprData::Variable(
                                            4,
                                        ),
                                        HirEagerExprData::Variable(
                                            10,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 49,
                                            ident: `cross`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    50,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::MethodCall {
                                            self_argument: 48,
                                            ident: `max`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    51,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::Binary {
                                            lopd: 47,
                                            opr: Assign,
                                            ropd: 52,
                                        },
                                        HirEagerExprData::Literal(
                                            TermLiteral::F32(
                                                NotNan(
                                                    999999.0,
                                                ),
                                            ),
                                        ),
                                        HirEagerExprData::Prefix {
                                            opr: Minus,
                                            opd_hir_expr_idx: 54,
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 56,
                                            ident: `strokes`,
                                        },
                                        HirEagerExprData::Variable(
                                            2,
                                        ),
                                        HirEagerExprData::Variable(
                                            3,
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 58,
                                            opr: Closed(
                                                RemEuclid,
                                            ),
                                            ropd: 59,
                                        },
                                        HirEagerExprData::Index {
                                            owner_hir_expr_idx: 57,
                                            items: [
                                                60,
                                            ],
                                        },
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 61,
                                            ident: `points`,
                                        },
                                        HirEagerExprData::Variable(
                                            12,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 63,
                                            ident: `start`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            12,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 65,
                                            ident: `end`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            1,
                                        ),
                                        HirEagerExprData::Field {
                                            owner_hir_expr_idx: 67,
                                            ident: `contour`,
                                        },
                                        HirEagerExprData::Variable(
                                            8,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 69,
                                            ident: `start`,
                                            template_arguments: None,
                                            item_groups: [],
                                        },
                                        HirEagerExprData::Variable(
                                            13,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 68,
                                            ident: `displacement`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    70,
                                                ),
                                                Regular(
                                                    71,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::Variable(
                                            11,
                                        ),
                                        HirEagerExprData::Variable(
                                            11,
                                        ),
                                        HirEagerExprData::Variable(
                                            4,
                                        ),
                                        HirEagerExprData::Variable(
                                            14,
                                        ),
                                        HirEagerExprData::MethodCall {
                                            self_argument: 75,
                                            ident: `cross`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    76,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::MethodCall {
                                            self_argument: 74,
                                            ident: `max`,
                                            template_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    77,
                                                ),
                                            ],
                                        },
                                        HirEagerExprData::Binary {
                                            lopd: 73,
                                            opr: Assign,
                                            ropd: 78,
                                        },
                                        HirEagerExprData::Variable(
                                            11,
                                        ),
                                        HirEagerExprData::Variable(
                                            7,
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 80,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 81,
                                        },
                                        HirEagerExprData::Variable(
                                            6,
                                        ),
                                        HirEagerExprData::Literal(
                                            TermLiteral::I32(
                                                0,
                                            ),
                                        ),
                                        HirEagerExprData::Binary {
                                            lopd: 83,
                                            opr: Comparison(
                                                Greater,
                                            ),
                                            ropd: 84,
                                        },
                                        HirEagerExprData::Block {
                                            stmts: ArenaIdxRange(
                                                13..18,
                                            ),
                                        },
                                    ],
                                },
                                hir_eager_stmt_arena: Arena {
                                    data: [
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 7,
                                                ty: None,
                                            },
                                            initial_value: 46,
                                        },
                                        Eval {
                                            expr_idx: 53,
                                            discarded: false,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 10,
                                                ty: None,
                                            },
                                            initial_value: 72,
                                        },
                                        Eval {
                                            expr_idx: 79,
                                            discarded: false,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 5,
                                                ty: None,
                                            },
                                            initial_value: 27,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 6,
                                                ty: None,
                                            },
                                            initial_value: 36,
                                        },
                                        ForBetween {
                                            particulars: HirEagerForBetweenParticulars {
                                                frame_var_ident: Ident(
                                                    Coword(
                                                        Id {
                                                            value: 269,
                                                        },
                                                    ),
                                                ),
                                                range: HirEagerForBetweenRange {
                                                    initial_boundary: HirEagerForBetweenLoopBoundary {
                                                        bound_expr: Some(
                                                            38,
                                                        ),
                                                        kind: LowerClosed,
                                                    },
                                                    final_boundary: HirEagerForBetweenLoopBoundary {
                                                        bound_expr: Some(
                                                            40,
                                                        ),
                                                        kind: UpperOpen,
                                                    },
                                                    step: Constant(
                                                        1,
                                                    ),
                                                },
                                            },
                                            block: ArenaIdxRange(
                                                1..3,
                                            ),
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 8,
                                                ty: None,
                                            },
                                            initial_value: 55,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 9,
                                                ty: None,
                                            },
                                            initial_value: 62,
                                        },
                                        ForBetween {
                                            particulars: HirEagerForBetweenParticulars {
                                                frame_var_ident: Ident(
                                                    Coword(
                                                        Id {
                                                            value: 270,
                                                        },
                                                    ),
                                                ),
                                                range: HirEagerForBetweenRange {
                                                    initial_boundary: HirEagerForBetweenLoopBoundary {
                                                        bound_expr: Some(
                                                            64,
                                                        ),
                                                        kind: LowerClosed,
                                                    },
                                                    final_boundary: HirEagerForBetweenLoopBoundary {
                                                        bound_expr: Some(
                                                            66,
                                                        ),
                                                        kind: UpperOpen,
                                                    },
                                                    step: Constant(
                                                        1,
                                                    ),
                                                },
                                            },
                                            block: ArenaIdxRange(
                                                3..5,
                                            ),
                                        },
                                        Return {
                                            result: 82,
                                        },
                                        Return {
                                            result: 85,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 1,
                                                ty: None,
                                            },
                                            initial_value: 3,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 2,
                                                ty: None,
                                            },
                                            initial_value: 10,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 3,
                                                ty: None,
                                            },
                                            initial_value: 19,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 4,
                                                ty: None,
                                            },
                                            initial_value: 22,
                                        },
                                        IfElse {
                                            if_branch: HirEagerIfBranch {
                                                condition: HirEagerCondition(
                                                    25,
                                                ),
                                                stmts: ArenaIdxRange(
                                                    5..12,
                                                ),
                                            },
                                            elif_branches: [],
                                            else_branch: Some(
                                                HirEagerElseBranch {
                                                    stmts: ArenaIdxRange(
                                                        12..13,
                                                    ),
                                                },
                                            ),
                                        },
                                    ],
                                },
                                hir_eager_pattern_expr_arena: Arena {
                                    data: [
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 23,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 422,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 423,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 424,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: Some(
                                                Mut,
                                            ),
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 425,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 426,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 302,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: Some(
                                                Mut,
                                            ),
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 427,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 428,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            symbol_modifier: None,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 302,
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
                                                                value: 220,
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
                                                                value: 421,
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
                                                                value: 23,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 422,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 423,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 424,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 425,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 426,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 269,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LoopVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 302,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 427,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 428,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 270,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LoopVariable,
                                            },
                                            HirEagerVariable {
                                                name: Ident(
                                                    Ident(
                                                        Coword(
                                                            Id {
                                                                value: 302,
                                                            },
                                                        ),
                                                    ),
                                                ),
                                                data: LetVariable,
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