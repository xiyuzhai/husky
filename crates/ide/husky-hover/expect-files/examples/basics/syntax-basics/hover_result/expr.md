[
    (
        TokenIdx(
            1,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "This is a paradigm\ntoken_idx = 0;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Keyword(\n    Keyword::Fugitive(\n        Fn,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 0,
                                character: 0,
                            },
                            end: Position {
                                line: 0,
                                character: 2,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            3,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 2;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Bra(\n            Delimiter::Par,\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 0,
                                character: 9,
                            },
                            end: Position {
                                line: 0,
                                character: 10,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            5,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 4;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Colon,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 0,
                                character: 11,
                            },
                            end: Position {
                                line: 0,
                                character: 12,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            7,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 6;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Ident(\n    `t`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::PatternExpr(\n            1,\n        ),\n        data: TokenInfoData::CurrentSynSymbol {\n            current_syn_symbol_idx: 1,\n            current_syn_symbol_kind: CurrentSynSymbolKind::LetVariable {\n                pattern_symbol_idx: 1,\n            },\n            syn_expr_region: ExprRegionLeash(_),\n        },\n    },\n);\n\nCurrentSynSymbol {\n    modifier: Pure,\n    access_start: RegionalTokenIdx(\n        3,\n    ),\n    access_end: Some(\n        RegionalTokenIdxRangeEnd(\n            RegionalTokenIdx(\n                7,\n            ),\n        ),\n    ),\n    data: CurrentSynSymbolData::LetVariable {\n        ident: `t`,\n        pattern_symbol_idx: 1,\n    },\n}\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 1,
                                character: 8,
                            },
                            end: Position {
                                line: 1,
                                character: 9,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            9,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 8;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Bra(\n            Delimiter::BlockCurl,\n        ),\n    ),\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SemaExpr(\n            SemaExprIdx(\n                2,\n            ),\n        ),\n        data: TokenInfoData::NestedBlockCurl,\n    },\n);\n\nNestedBlockCurl\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 1,
                                character: 12,
                            },
                            end: Position {
                                line: 1,
                                character: 13,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            11,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 10;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Ket(\n            Delimiter::BlockCurl,\n        ),\n    ),\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SemaExpr(\n            SemaExprIdx(\n                2,\n            ),\n        ),\n        data: TokenInfoData::NestedBlockCurl,\n    },\n);\n\nNestedBlockCurl\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 3,
                                character: 4,
                            },
                            end: Position {
                                line: 3,
                                character: 5,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            13,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 12;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Ident(\n    `closure_inline`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::AstIdentifiable,\n        data: TokenInfoData::EntityNode(\n            ItemSynNodePath::MajorItem(\n                MajorItemSynNodePath::Fugitive(\n                    FugitiveSynNodePath(`syntax_basics::expr::closure_inline`, `Ritchie(\n                        Fn,\n                    )`, (0)),\n                ),\n            ),\n            EntityKind::MajorItem {\n                module_item_kind: MajorItemKind::Fugitive(\n                    MajorFugitiveKind::Ritchie(\n                        Fn,\n                    ),\n                ),\n                connection: MajorItemConnectionKind::Connected,\n            },\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 5,
                                character: 3,
                            },
                            end: Position {
                                line: 5,
                                character: 17,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            15,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 14;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Ket(\n            Delimiter::Par,\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 5,
                                character: 18,
                            },
                            end: Position {
                                line: 5,
                                character: 19,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            17,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 16;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Keyword(\n    Keyword::Stmt(\n        Let,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 4,
                            },
                            end: Position {
                                line: 6,
                                character: 7,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            19,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 18;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Eq,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 10,
                            },
                            end: Position {
                                line: 6,
                                character: 11,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            21,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 20;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Ident(\n    `x`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::PatternExpr(\n            2,\n        ),\n        data: TokenInfoData::CurrentSynSymbol {\n            current_syn_symbol_idx: 2,\n            current_syn_symbol_kind: CurrentSynSymbolKind::SimpleClosureParameter {\n                pattern_symbol_idx: 2,\n            },\n            syn_expr_region: ExprRegionLeash(_),\n        },\n    },\n);\n\nCurrentSynSymbol {\n    modifier: Pure,\n    access_start: RegionalTokenIdx(\n        6,\n    ),\n    access_end: Some(\n        RegionalTokenIdxRangeEnd(\n            RegionalTokenIdx(\n                12,\n            ),\n        ),\n    ),\n    data: CurrentSynSymbolData::SimpleClosureParameter {\n        ident: `x`,\n        pattern_symbol_idx: 2,\n    },\n}\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 13,
                            },
                            end: Position {
                                line: 6,
                                character: 14,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            23,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 22;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Ident(\n    `i32`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SynPrincipalEntityPathExpr(\n            1,\n            PrincipalEntityPath::MajorItem(\n                MajorItemPath::Type(\n                    TypePath(`core::num::i32`, `Extern`),\n                ),\n            ),\n        ),\n        data: TokenInfoData::Entity(\n            EntityPath::MajorItem(\n                MajorItemPath::Type(\n                    TypePath(`core::num::i32`, `Extern`),\n                ),\n            ),\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 16,
                            },
                            end: Position {
                                line: 6,
                                character: 19,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            25,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 24;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Ident(\n    `x`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SemaExpr(\n            SemaExprIdx(\n                3,\n            ),\n        ),\n        data: TokenInfoData::CurrentSynSymbol {\n            current_syn_symbol_idx: 2,\n            current_syn_symbol_kind: CurrentSynSymbolKind::SimpleClosureParameter {\n                pattern_symbol_idx: 2,\n            },\n            syn_expr_region: ExprRegionLeash(_),\n        },\n    },\n);\n\nCurrentSynSymbol {\n    modifier: Pure,\n    access_start: RegionalTokenIdx(\n        6,\n    ),\n    access_end: Some(\n        RegionalTokenIdxRangeEnd(\n            RegionalTokenIdx(\n                12,\n            ),\n        ),\n    ),\n    data: CurrentSynSymbolData::SimpleClosureParameter {\n        ident: `x`,\n        pattern_symbol_idx: 2,\n    },\n}\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 21,
                            },
                            end: Position {
                                line: 6,
                                character: 22,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            27,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 26;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Literal(\n    LiteralTokenData::Integer(\n        UnspecifiedRegular(\n            1,\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 6,
                                character: 25,
                            },
                            end: Position {
                                line: 6,
                                character: 26,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            29,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 28;\n\ntoken_line_group_idx = 4\n\ntoken = TokenData::Ident(\n    `closure_nested`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::AstIdentifiable,\n        data: TokenInfoData::EntityNode(\n            ItemSynNodePath::MajorItem(\n                MajorItemSynNodePath::Fugitive(\n                    FugitiveSynNodePath(`syntax_basics::expr::closure_nested`, `Ritchie(\n                        Fn,\n                    )`, (0)),\n                ),\n            ),\n            EntityKind::MajorItem {\n                module_item_kind: MajorItemKind::Fugitive(\n                    MajorFugitiveKind::Ritchie(\n                        Fn,\n                    ),\n                ),\n                connection: MajorItemConnectionKind::Connected,\n            },\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 8,
                                character: 3,
                            },
                            end: Position {
                                line: 8,
                                character: 17,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            31,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 30;\n\ntoken_line_group_idx = 4\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Ket(\n            Delimiter::Par,\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 8,
                                character: 18,
                            },
                            end: Position {
                                line: 8,
                                character: 19,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            33,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 32;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Keyword(\n    Keyword::Stmt(\n        Let,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 9,
                                character: 4,
                            },
                            end: Position {
                                line: 9,
                                character: 7,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            35,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 34;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Eq,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 9,
                                character: 10,
                            },
                            end: Position {
                                line: 9,
                                character: 11,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            37,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 36;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Ident(\n    `x`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::PatternExpr(\n            2,\n        ),\n        data: TokenInfoData::CurrentSynSymbol {\n            current_syn_symbol_idx: 2,\n            current_syn_symbol_kind: CurrentSynSymbolKind::SimpleClosureParameter {\n                pattern_symbol_idx: 2,\n            },\n            syn_expr_region: ExprRegionLeash(_),\n        },\n    },\n);\n\nCurrentSynSymbol {\n    modifier: Pure,\n    access_start: RegionalTokenIdx(\n        6,\n    ),\n    access_end: Some(\n        RegionalTokenIdxRangeEnd(\n            RegionalTokenIdx(\n                14,\n            ),\n        ),\n    ),\n    data: CurrentSynSymbolData::SimpleClosureParameter {\n        ident: `x`,\n        pattern_symbol_idx: 2,\n    },\n}\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 9,
                                character: 13,
                            },
                            end: Position {
                                line: 9,
                                character: 14,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            39,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 38;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Ident(\n    `i32`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SynPrincipalEntityPathExpr(\n            1,\n            PrincipalEntityPath::MajorItem(\n                MajorItemPath::Type(\n                    TypePath(`core::num::i32`, `Extern`),\n                ),\n            ),\n        ),\n        data: TokenInfoData::Entity(\n            EntityPath::MajorItem(\n                MajorItemPath::Type(\n                    TypePath(`core::num::i32`, `Extern`),\n                ),\n            ),\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 9,
                                character: 16,
                            },
                            end: Position {
                                line: 9,
                                character: 19,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            41,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 40;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Bra(\n            Delimiter::BlockCurl,\n        ),\n    ),\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SemaExpr(\n            SemaExprIdx(\n                6,\n            ),\n        ),\n        data: TokenInfoData::NestedBlockCurl,\n    },\n);\n\nNestedBlockCurl\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 9,
                                character: 21,
                            },
                            end: Position {
                                line: 9,
                                character: 22,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            43,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 42;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Binary(\n            SynBinaryOpr::Closed(\n                BinaryClosedOpr::Add,\n            ),\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 10,
                                character: 10,
                            },
                            end: Position {
                                line: 10,
                                character: 11,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
    (
        TokenIdx(
            45,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 44;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Ket(\n            Delimiter::BlockCurl,\n        ),\n    ),\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::SemaExpr(\n            SemaExprIdx(\n                6,\n            ),\n        ),\n        data: TokenInfoData::NestedBlockCurl,\n    },\n);\n\nNestedBlockCurl\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 11,
                                character: 4,
                            },
                            end: Position {
                                line: 11,
                                character: 5,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
]