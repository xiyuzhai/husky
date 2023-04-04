Ok(
    EntityTreeSheet {
        module_path: `mnist_classifier::line_segment_sketch::convex_component`,
        symbols: EntitySymbolTable(
            [
                EntitySymbolEntry {
                    ident: `ConvexComponent`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::ModuleItem(
                        ModuleItemSymbol {
                            path: ModuleItemPath::Type(
                                TypePath(`mnist_classifier::line_segment_sketch::convex_component::ConvexComponent`, `Struct`),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 3,
                            ident_token: IdentToken {
                                ident: `ConvexComponent`,
                                token_idx: TokenIdx(
                                    7,
                                ),
                            },
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `concave_component`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Submodule(
                                SubmoduleSymbol {
                                    path: `mnist_classifier::line_segment_sketch::concave_component`,
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 159,
                                    ident_token: IdentToken {
                                        ident: `concave_component`,
                                        token_idx: TokenIdx(
                                            1,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::Module(
                                `mnist_classifier::line_segment_sketch::concave_component`,
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `convex_component`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Submodule(
                                SubmoduleSymbol {
                                    path: `mnist_classifier::line_segment_sketch::convex_component`,
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 160,
                                    ident_token: IdentToken {
                                        ident: `convex_component`,
                                        token_idx: TokenIdx(
                                            3,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::Module(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `convexity`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Submodule(
                                SubmoduleSymbol {
                                    path: `mnist_classifier::line_segment_sketch::convexity`,
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 161,
                                    ident_token: IdentToken {
                                        ident: `convexity`,
                                        token_idx: TokenIdx(
                                            5,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::Module(
                                `mnist_classifier::line_segment_sketch::convexity`,
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `line_segment`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Submodule(
                                SubmoduleSymbol {
                                    path: `mnist_classifier::line_segment_sketch::line_segment`,
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 162,
                                    ident_token: IdentToken {
                                        ident: `line_segment`,
                                        token_idx: TokenIdx(
                                            7,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::Module(
                                `mnist_classifier::line_segment_sketch::line_segment`,
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `LineSegmentStroke`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Type(
                                        TypePath(`mnist_classifier::line_segment_sketch::LineSegmentStroke`, `Struct`),
                                    ),
                                    visibility: Visibility::Pub,
                                    ast_idx: 169,
                                    ident_token: IdentToken {
                                        ident: `LineSegmentStroke`,
                                        token_idx: TokenIdx(
                                            41,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::line_segment_sketch::LineSegmentStroke`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `LineSegmentSketch`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Type(
                                        TypePath(`mnist_classifier::line_segment_sketch::LineSegmentSketch`, `Struct`),
                                    ),
                                    visibility: Visibility::Pub,
                                    ast_idx: 171,
                                    ident_token: IdentToken {
                                        ident: `LineSegmentSketch`,
                                        token_idx: TokenIdx(
                                            161,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::line_segment_sketch::LineSegmentSketch`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `go_right`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Form(
                                        FormPath(`mnist_classifier::line_segment_sketch::go_right`, `Fn`),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 173,
                                    ident_token: IdentToken {
                                        ident: `go_right`,
                                        token_idx: TokenIdx(
                                            348,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::go_right`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `go_left`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Form(
                                        FormPath(`mnist_classifier::line_segment_sketch::go_left`, `Fn`),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 174,
                                    ident_token: IdentToken {
                                        ident: `go_left`,
                                        token_idx: TokenIdx(
                                            445,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::go_left`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `extend_end`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Form(
                                        FormPath(`mnist_classifier::line_segment_sketch::extend_end`, `Fn`),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 175,
                                    ident_token: IdentToken {
                                        ident: `extend_end`,
                                        token_idx: TokenIdx(
                                            542,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::extend_end`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `extend_start`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Form(
                                        FormPath(`mnist_classifier::line_segment_sketch::extend_start`, `Fn`),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 176,
                                    ident_token: IdentToken {
                                        ident: `extend_start`,
                                        token_idx: TokenIdx(
                                            775,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::extend_start`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `find_line_segments`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::ModuleItem(
                                ModuleItemSymbol {
                                    path: ModuleItemPath::Form(
                                        FormPath(`mnist_classifier::line_segment_sketch::find_line_segments`, `Fn`),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 177,
                                    ident_token: IdentToken {
                                        ident: `find_line_segments`,
                                        token_idx: TokenIdx(
                                            1041,
                                        ),
                                    },
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::find_line_segments`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `ConcaveComponent`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 74,
                                            ident_token: IdentToken {
                                                ident: `ConcaveComponent`,
                                                token_idx: TokenIdx(
                                                    34,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::Pub,
                                    ast_idx: 163,
                                    use_expr_idx: 0,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `find_concave_components`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Form(
                                                FormPath(`mnist_classifier::line_segment_sketch::concave_component::find_concave_components`, `Fn`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 76,
                                            ident_token: IdentToken {
                                                ident: `find_concave_components`,
                                                token_idx: TokenIdx(
                                                    522,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Form(
                                            FormPath(`mnist_classifier::line_segment_sketch::concave_component::find_concave_components`, `Fn`),
                                        ),
                                    ),
                                    visibility: Visibility::Pub,
                                    ast_idx: 163,
                                    use_expr_idx: 0,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Form(
                                    FormPath(`mnist_classifier::line_segment_sketch::concave_component::find_concave_components`, `Fn`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `LineSegment`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::line_segment_sketch::line_segment::LineSegment`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 16,
                                            ident_token: IdentToken {
                                                ident: `LineSegment`,
                                                token_idx: TokenIdx(
                                                    8,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::line_segment_sketch::line_segment::LineSegment`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::Pub,
                                    ast_idx: 165,
                                    use_expr_idx: 4,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::line_segment_sketch::line_segment::LineSegment`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `RawContour`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::raw_contour::RawContour`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 203,
                                            ident_token: IdentToken {
                                                ident: `RawContour`,
                                                token_idx: TokenIdx(
                                                    24,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::raw_contour::RawContour`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 167,
                                    use_expr_idx: 9,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::raw_contour::RawContour`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `Point2d`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::Point2d`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 78,
                                            ident_token: IdentToken {
                                                ident: `Point2d`,
                                                token_idx: TokenIdx(
                                                    2,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::Point2d`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::Point2d`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `RelativePoint2d`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::RelativePoint2d`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 80,
                                            ident_token: IdentToken {
                                                ident: `RelativePoint2d`,
                                                token_idx: TokenIdx(
                                                    144,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::RelativePoint2d`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::RelativePoint2d`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `Vector2d`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::Vector2d`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 81,
                                            ident_token: IdentToken {
                                                ident: `Vector2d`,
                                                token_idx: TokenIdx(
                                                    157,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::Vector2d`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::Vector2d`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `ClosedRange`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::ClosedRange`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 83,
                                            ident_token: IdentToken {
                                                ident: `ClosedRange`,
                                                token_idx: TokenIdx(
                                                    488,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::ClosedRange`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::ClosedRange`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `BoundingBox`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::BoundingBox`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 85,
                                            ident_token: IdentToken {
                                                ident: `BoundingBox`,
                                                token_idx: TokenIdx(
                                                    596,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::BoundingBox`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::BoundingBox`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
                EntitySymbolEntry {
                    ident: `RelativeBoundingBox`,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    symbol: EntitySymbol::Use(
                        UseSymbol {
                            original_symbol: EntitySymbol::Use(
                                UseSymbol {
                                    original_symbol: EntitySymbol::ModuleItem(
                                        ModuleItemSymbol {
                                            path: ModuleItemPath::Type(
                                                TypePath(`mnist_classifier::geom2d::RelativeBoundingBox`, `Struct`),
                                            ),
                                            visibility: Visibility::Pub,
                                            ast_idx: 87,
                                            ident_token: IdentToken {
                                                ident: `RelativeBoundingBox`,
                                                token_idx: TokenIdx(
                                                    732,
                                                ),
                                            },
                                        },
                                    ),
                                    path: EntityPath::ModuleItem(
                                        ModuleItemPath::Type(
                                            TypePath(`mnist_classifier::geom2d::RelativeBoundingBox`, `Struct`),
                                        ),
                                    ),
                                    visibility: Visibility::PubUnder(
                                        `mnist_classifier::line_segment_sketch`,
                                    ),
                                    ast_idx: 166,
                                    use_expr_idx: 6,
                                },
                            ),
                            path: EntityPath::ModuleItem(
                                ModuleItemPath::Type(
                                    TypePath(`mnist_classifier::geom2d::RelativeBoundingBox`, `Struct`),
                                ),
                            ),
                            visibility: Visibility::PubUnder(
                                `mnist_classifier::line_segment_sketch::convex_component`,
                            ),
                            ast_idx: 2,
                            use_expr_idx: 0,
                        },
                    ),
                },
            ],
        ),
        impl_blocks: [
            ImplBlock::Type(
                TypeImplBlock {
                    id: TypeImplBlockId {
                        module_path: `mnist_classifier::line_segment_sketch::convex_component`,
                        ty_path: TypePath(`mnist_classifier::line_segment_sketch::convex_component::ConvexComponent`, `Struct`),
                        disambiguator: 0,
                    },
                    ast_idx: 4,
                    impl_token: ImplToken {
                        token_idx: TokenIdx(
                            22,
                        ),
                    },
                    ty_expr: 9,
                    body: Type(
                        TypeItems {
                            ast_idx_range: ArenaIdxRange(
                                0..2,
                            ),
                        },
                    ),
                },
            ),
        ],
        use_expr_rules: UseExprRules(
            [
                UseExprRule {
                    ast_idx: 2,
                    use_expr_idx: 2,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    variant: UseExprRuleVariant::Parent {
                        parent_name_token: NameToken::Crate(
                            CrateToken {
                                token_idx: TokenIdx(
                                    1,
                                ),
                            },
                        ),
                        children: ArenaIdxRange(
                            1..2,
                        ),
                    },
                    parent: None,
                    state: UseExprRuleState::Resolved {
                        original_symbol: EntitySymbol::CrateRoot {
                            root_module_path: `mnist_classifier`,
                        },
                    },
                },
                UseExprRule {
                    ast_idx: 2,
                    use_expr_idx: 1,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    variant: UseExprRuleVariant::Parent {
                        parent_name_token: NameToken::Ident(
                            IdentToken {
                                ident: `line_segment_sketch`,
                                token_idx: TokenIdx(
                                    3,
                                ),
                            },
                        ),
                        children: ArenaIdxRange(
                            0..1,
                        ),
                    },
                    parent: Some(
                        EntityPath::Module(
                            `mnist_classifier`,
                        ),
                    ),
                    state: UseExprRuleState::Resolved {
                        original_symbol: EntitySymbol::Submodule(
                            SubmoduleSymbol {
                                path: `mnist_classifier::line_segment_sketch`,
                                visibility: Visibility::PubUnder(
                                    `mnist_classifier`,
                                ),
                                ast_idx: 14,
                                ident_token: IdentToken {
                                    ident: `line_segment_sketch`,
                                    token_idx: TokenIdx(
                                        7,
                                    ),
                                },
                            },
                        ),
                    },
                },
            ],
        ),
        use_all_rules: UseAllRules(
            [
                UseAllRule {
                    parent: KinshipedModulePath {
                        kinship: Inside,
                        path: `mnist_classifier::line_segment_sketch`,
                    },
                    ast_idx: 2,
                    use_expr_idx: 0,
                    visibility: Visibility::PubUnder(
                        `mnist_classifier::line_segment_sketch::convex_component`,
                    ),
                    progress: 21,
                },
            ],
        ),
        errors: [],
    },
)