[
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Val(
                ValHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::simple_seven_match`, `Val`),
                    hir_decl: ValFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::simple_seven_match`, `Val`),
                        hir_expr_region: Eager(
                            HirEagerExprRegion(
                                Id {
                                    value: 1,
                                },
                            ),
                        ),
                    },
                    body_with_hir_expr_region: Some(
                        (
                            Eager(
                                6,
                            ),
                            Eager(
                                HirEagerExprRegion(
                                    Id {
                                        value: 41,
                                    },
                                ),
                            ),
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Fn(
                FnHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::simple_leftdown_pattern`, `Fn`),
                    hir_decl: FnFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::simple_leftdown_pattern`, `Fn`),
                        template_parameters: HirTemplateParameters {
                            data: [],
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            10,
                            HirEagerExprRegion {
                                expr_arena: Arena {
                                    data: [
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 1,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 300,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 3,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 274,
                                                    },
                                                ),
                                            ),
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    0.0,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 4,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 5,
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 7,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 274,
                                                    },
                                                ),
                                            ),
                                        },
                                        Prefix {
                                            opr: Minus,
                                            opd: 8,
                                        },
                                        Block {
                                            stmts: ArenaIdxRange(
                                                1..4,
                                            ),
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 1,
                                                ty: None,
                                            },
                                            initial_value: 2,
                                        },
                                        Require {
                                            condition: 6,
                                        },
                                        Eval {
                                            expr_idx: 9,
                                        },
                                    ],
                                },
                                pattern_expr_arena: Arena {
                                    data: [
                                        Ident {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                    ],
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Val(
                ValHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::special_seven_match`, `Val`),
                    hir_decl: ValFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::special_seven_match`, `Val`),
                        hir_expr_region: Eager(
                            HirEagerExprRegion(
                                Id {
                                    value: 1,
                                },
                            ),
                        ),
                    },
                    body_with_hir_expr_region: Some(
                        (
                            Eager(
                                7,
                            ),
                            Eager(
                                HirEagerExprRegion(
                                    Id {
                                        value: 43,
                                    },
                                ),
                            ),
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Fn(
                FnHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::leftupcc_pattern`, `Fn`),
                    hir_decl: FnFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::leftupcc_pattern`, `Fn`),
                        template_parameters: HirTemplateParameters {
                            data: [],
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            15,
                            HirEagerExprRegion {
                                expr_arena: Arena {
                                    data: [
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 1,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 300,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 3,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 274,
                                                    },
                                                ),
                                            ),
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    0.0,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 4,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 5,
                                        },
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 7,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 298,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 8,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 295,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    0.6,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 9,
                                            opr: Comparison(
                                                Greater,
                                            ),
                                            ropd: 10,
                                        },
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 12,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 147,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        Field {
                                            owner: 13,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 274,
                                                    },
                                                ),
                                            ),
                                        },
                                        Block {
                                            stmts: ArenaIdxRange(
                                                1..5,
                                            ),
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 1,
                                                ty: None,
                                            },
                                            initial_value: 2,
                                        },
                                        Require {
                                            condition: 6,
                                        },
                                        Require {
                                            condition: 11,
                                        },
                                        Eval {
                                            expr_idx: 14,
                                        },
                                    ],
                                },
                                pattern_expr_arena: Arena {
                                    data: [
                                        Ident {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                    ],
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Fn(
                FnHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::leftdowncc_pattern`, `Fn`),
                    hir_decl: FnFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::leftdowncc_pattern`, `Fn`),
                        template_parameters: HirTemplateParameters {
                            data: [],
                        },
                    },
                    eager_body_with_hir_eager_expr_region: Some(
                        (
                            20,
                            HirEagerExprRegion {
                                expr_arena: Arena {
                                    data: [
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 1,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 300,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 3,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 274,
                                                    },
                                                ),
                                            ),
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    0.0,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 4,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 5,
                                        },
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        Field {
                                            owner: 7,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 298,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 8,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 294,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    0.3,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 9,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 10,
                                        },
                                        InheritedSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 284,
                                                    },
                                                ),
                                            ),
                                        },
                                        MethodCall {
                                            self_argument: 12,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 415,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [],
                                        },
                                        Literal(
                                            Bool(
                                                true,
                                            ),
                                        ),
                                        MethodCall {
                                            self_argument: 13,
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 356,
                                                    },
                                                ),
                                            ),
                                            generic_arguments: None,
                                            item_groups: [
                                                Regular(
                                                    14,
                                                ),
                                            ],
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 510,
                                                    },
                                                ),
                                            ),
                                        },
                                        Literal(
                                            F32(
                                                NotNan(
                                                    30.0,
                                                ),
                                            ),
                                        ),
                                        Binary {
                                            lopd: 16,
                                            opr: Comparison(
                                                Less,
                                            ),
                                            ropd: 17,
                                        },
                                        CurrentSymbol {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 510,
                                                    },
                                                ),
                                            ),
                                        },
                                        Block {
                                            stmts: ArenaIdxRange(
                                                1..7,
                                            ),
                                        },
                                    ],
                                },
                                stmt_arena: Arena {
                                    data: [
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 1,
                                                ty: None,
                                            },
                                            initial_value: 2,
                                        },
                                        Require {
                                            condition: 6,
                                        },
                                        Require {
                                            condition: 11,
                                        },
                                        Let {
                                            pattern: HirEagerLetVariablesPattern {
                                                pattern_expr_idx: 2,
                                                ty: None,
                                            },
                                            initial_value: 15,
                                        },
                                        Require {
                                            condition: 18,
                                        },
                                        Eval {
                                            expr_idx: 19,
                                        },
                                    ],
                                },
                                pattern_expr_arena: Arena {
                                    data: [
                                        Ident {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 386,
                                                    },
                                                ),
                                            ),
                                        },
                                        Ident {
                                            ident: Ident(
                                                Coword(
                                                    Id {
                                                        value: 510,
                                                    },
                                                ),
                                            ),
                                        },
                                    ],
                                },
                            },
                        ),
                    ),
                },
            ),
        ),
    ),
    HirDefn::MajorItem(
        MajorItemHirDefn::Fugitive(
            FugitiveHirDefn::Val(
                ValHirDefn {
                    path: FugitivePath(`mnist_classifier::digits::seven::is_seven`, `Val`),
                    hir_decl: ValFugitiveHirDecl {
                        path: FugitivePath(`mnist_classifier::digits::seven::is_seven`, `Val`),
                        hir_expr_region: Eager(
                            HirEagerExprRegion(
                                Id {
                                    value: 1,
                                },
                            ),
                        ),
                    },
                    body_with_hir_expr_region: Some(
                        (
                            Eager(
                                61,
                            ),
                            Eager(
                                HirEagerExprRegion(
                                    Id {
                                        value: 46,
                                    },
                                ),
                            ),
                        ),
                    ),
                },
            ),
        ),
    ),
]