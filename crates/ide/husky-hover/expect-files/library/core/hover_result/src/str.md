```rust
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
                            value: "Other\ntoken_idx = 0;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Keyword(\n    Keyword::Use,\n);\n\ntoken_info = None;\n\n\n",
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
                                character: 3,
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
            2,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 1;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Keyword(\n    Keyword::Pronoun(\n        Crate,\n    ),\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::UseExpr(\n            1,\n        ),\n        data: TokenInfoData::UseExpr {\n            use_expr_idx: 1,\n            rule_idx: OnceUseRuleIdx(\n                0,\n            ),\n            state: UseOneRuleState::Resolved {\n                original_symbol: Some(\n                    EntitySymbol::CrateRoot {\n                        root_module_path: ModulePath(`core`),\n                    },\n                ),\n            },\n        },\n    },\n);\n\nuse\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 0,
                                character: 4,
                            },
                            end: Position {
                                line: 0,
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
            3,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 2;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Binary(\n            SynBinaryOpr::ScopeResolution,\n        ),\n    ),\n);\n\ntoken_info = None;\n\n\n",
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
            4,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 3;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Star,\n    ),\n);\n\ntoken_info = None;\n\n\n",
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
            5,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 4;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Keyword(\n    Keyword::Pub,\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 2,
                                character: 0,
                            },
                            end: Position {
                                line: 2,
                                character: 3,
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
            6,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 5;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Keyword(\n    Keyword::TypeEntity(\n        Extern,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 2,
                                character: 4,
                            },
                            end: Position {
                                line: 2,
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
            7,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 6;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Ident(\n    `str`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::AstIdentifiable,\n        data: TokenInfoData::EntityNode(\n            ItemSynNodePath::MajorItem(\n                MajorItemSynNodePath::Type(\n                    TypeSynNodePath(\n                        ItemSynNodePathId {\n                            data: ItemSynNodePathData::MajorItem(\n                                MajorItemSynNodePathData::Type(\n                                    TypeSynNodePathData {\n                                        disambiguated_item_path: DisambiguatedItemPath {\n                                            maybe_ambiguous_item_path: TypePath(`core::str::str`, `Extern`),\n                                            disambiguator: 0,\n                                        },\n                                    },\n                                ),\n                            ),\n                        },\n                    ),\n                ),\n            ),\n            EntityKind::MajorItem {\n                module_item_kind: MajorItemKind::Type(\n                    TypeKind::Extern,\n                ),\n                connection: MajorItemConnectionKind::Connected,\n            },\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 2,
                                character: 11,
                            },
                            end: Position {
                                line: 2,
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
            8,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 7;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Semicolon,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 2,
                                character: 14,
                            },
                            end: Position {
                                line: 2,
                                character: 15,
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
                            value: "Other\ntoken_idx = 8;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Keyword(\n    Keyword::Pub,\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 3,
                                character: 0,
                            },
                            end: Position {
                                line: 3,
                                character: 3,
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
            10,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "Other\ntoken_idx = 9;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Keyword(\n    Keyword::TypeEntity(\n        Extern,\n    ),\n);\n\ntoken_info = None;\n\n\n",
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
            11,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 10;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Ident(\n    `StringLiteral`,\n);\n\ntoken_info = Some(\n    TokenInfo {\n        src: TokenInfoSource::AstIdentifiable,\n        data: TokenInfoData::EntityNode(\n            ItemSynNodePath::MajorItem(\n                MajorItemSynNodePath::Type(\n                    TypeSynNodePath(\n                        ItemSynNodePathId {\n                            data: ItemSynNodePathData::MajorItem(\n                                MajorItemSynNodePathData::Type(\n                                    TypeSynNodePathData {\n                                        disambiguated_item_path: DisambiguatedItemPath {\n                                            maybe_ambiguous_item_path: TypePath(`core::str::StringLiteral`, `Extern`),\n                                            disambiguator: 0,\n                                        },\n                                    },\n                                ),\n                            ),\n                        },\n                    ),\n                ),\n            ),\n            EntityKind::MajorItem {\n                module_item_kind: MajorItemKind::Type(\n                    TypeKind::Extern,\n                ),\n                connection: MajorItemConnectionKind::Connected,\n            },\n        ),\n    },\n);\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 3,
                                character: 11,
                            },
                            end: Position {
                                line: 3,
                                character: 24,
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
            12,
        ),
        Some(
            HoverResult {
                hover: Hover {
                    contents: Markup(
                        MarkupContent {
                            kind: Markdown,
                            value: "\ntoken_idx = 11;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Semicolon,\n    ),\n);\n\ntoken_info = None;\n\n\n",
                        },
                    ),
                    range: Some(
                        Range {
                            start: Position {
                                line: 3,
                                character: 24,
                            },
                            end: Position {
                                line: 3,
                                character: 25,
                            },
                        },
                    ),
                },
                actions: [],
            },
        ),
    ),
]
```