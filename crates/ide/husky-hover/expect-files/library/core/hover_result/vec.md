Ok(
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
                                value: "Other\ntoken_idx = 0;\n\ntoken_line_group_idx = 0\n\ntoken = TokenData::Keyword(\n    Keyword::Use,\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
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
                7,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 6;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Bra(\n            Par,\n        ),\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 3,
                                    character: 7,
                                },
                                end: Position {
                                    line: 3,
                                    character: 8,
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
                                value: "\ntoken_idx = 12;\n\ntoken_line_group_idx = 1\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Ket(\n            Par,\n        ),\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 3,
                                    character: 31,
                                },
                                end: Position {
                                    line: 3,
                                    character: 32,
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
                                value: "\ntoken_idx = 18;\n\ntoken_line_group_idx = 2\n\ntoken = TokenData::Ident(\n    `E`,\n);\n\ntoken_info = TokenInfo::CurrentSymbol {\n    current_symbol_idx: 1,\n    current_symbol_kind: CurrentSynSymbolKind::ImplicitParameter {\n        template_parameter_kind: CurrentImplicitParameterSynSymbolKind::Type {\n            ident_token: IdentRegionalToken {\n                ident: `E`,\n                regional_token_idx: RegionalTokenIdx(\n                    6,\n                ),\n            },\n        },\n    },\n    syn_expr_region: ExprRegionLeash(_),\n};\n\nCurrentSynSymbol {\n    modifier: Const,\n    access_start: RegionalTokenIdx(\n        7,\n    ),\n    access_end: None,\n    variant: CurrentSynSymbolVariant::TemplateParameter {\n        syn_attrs: TemplateParameterSynAttrs {\n            syn_attrs: [],\n        },\n        annotated_variance_token: Some(\n            VarianceRegionalToken::Covariant(\n                CovariantRegionalToken {\n                    regional_token_idx: RegionalTokenIdx(\n                        5,\n                    ),\n                },\n            ),\n        ),\n        template_parameter_variant: CurrentTemplateParameterSynSymbolVariant::Type {\n            ident_token: IdentRegionalToken {\n                ident: `E`,\n                regional_token_idx: RegionalTokenIdx(\n                    6,\n                ),\n            },\n        },\n    },\n}\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 4,
                                    character: 25,
                                },
                                end: Position {
                                    line: 4,
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
                25,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 24;\n\ntoken_line_group_idx = 3\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::RaOrGt,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 6,
                                    character: 6,
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
                31,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 30;\n\ntoken_line_group_idx = 4\n\ntoken = TokenData::Ident(\n    `ilen`,\n);\n\ntoken_info = TokenInfo::EntityNode(\n    ItemSynNodePath::AssociatedItem(\n        AssociatedItemSynNodePath::TypeItem(\n            TypeItemSynNodePath {\n                maybe_ambiguous_path: MaybeAmbiguousPath {\n                    path: TypeItemPath {\n                        impl_block: TypeImplBlockPath {\n                            module_path: `core::vec`,\n                            ty_path: TypePath(`core::vec::Vec`, `Extern`),\n                            disambiguator: 0,\n                        },\n                        ident: `ilen`,\n                        item_kind: MethodFn,\n                    },\n                    disambiguator: 0,\n                },\n            },\n        ),\n    ),\n    AssociatedItem {\n        associated_item_kind: TypeItem(\n            MethodFn,\n        ),\n    },\n);\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 7,
                                    character: 11,
                                },
                                end: Position {
                                    line: 7,
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
                37,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "Other\ntoken_idx = 36;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Keyword(\n    Keyword::Pub,\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
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
                43,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "Other\ntoken_idx = 42;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Keyword(\n    Keyword::Pronoun(\n        SelfValue,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
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
                                    character: 25,
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
                49,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 48;\n\ntoken_line_group_idx = 5\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Semicolon,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 9,
                                    character: 32,
                                },
                                end: Position {
                                    line: 9,
                                    character: 33,
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
                55,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 54;\n\ntoken_line_group_idx = 6\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Binary(\n            Curry,\n        ),\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 11,
                                    character: 19,
                                },
                                end: Position {
                                    line: 11,
                                    character: 21,
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
                61,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 60;\n\ntoken_line_group_idx = 7\n\ntoken = TokenData::Ident(\n    `last`,\n);\n\ntoken_info = TokenInfo::EntityNode(\n    ItemSynNodePath::AssociatedItem(\n        AssociatedItemSynNodePath::TypeItem(\n            TypeItemSynNodePath {\n                maybe_ambiguous_path: MaybeAmbiguousPath {\n                    path: TypeItemPath {\n                        impl_block: TypeImplBlockPath {\n                            module_path: `core::vec`,\n                            ty_path: TypePath(`core::vec::Vec`, `Extern`),\n                            disambiguator: 0,\n                        },\n                        ident: `last`,\n                        item_kind: MethodFn,\n                    },\n                    disambiguator: 0,\n                },\n            },\n        ),\n    ),\n    AssociatedItem {\n        associated_item_kind: TypeItem(\n            MethodFn,\n        ),\n    },\n);\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 13,
                                    character: 11,
                                },
                                end: Position {
                                    line: 13,
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
                67,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 66;\n\ntoken_line_group_idx = 7\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Semicolon,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 13,
                                    character: 29,
                                },
                                end: Position {
                                    line: 13,
                                    character: 30,
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
                73,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "Other\ntoken_idx = 72;\n\ntoken_line_group_idx = 8\n\ntoken = TokenData::Keyword(\n    Keyword::Modifier(\n        Mut,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 15,
                                    character: 16,
                                },
                                end: Position {
                                    line: 15,
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
                79,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 78;\n\ntoken_line_group_idx = 8\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Semicolon,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 15,
                                    character: 37,
                                },
                                end: Position {
                                    line: 15,
                                    character: 38,
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
                85,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "Other\ntoken_idx = 84;\n\ntoken_line_group_idx = 9\n\ntoken = TokenData::Keyword(\n    Keyword::Pronoun(\n        SelfValue,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 17,
                                    character: 28,
                                },
                                end: Position {
                                    line: 17,
                                    character: 32,
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
                91,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 90;\n\ntoken_line_group_idx = 9\n\ntoken = TokenData::Ident(\n    `E`,\n);\n\ntoken_info = TokenInfo::InheritedSymbol {\n    inherited_symbol_idx: 1,\n    inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(\n        InheritedTemplateParameterSynSymbol::Type {\n            ident: `E`,\n        },\n    ),\n    syn_expr_region: ExprRegionLeash(_),\n};\n\nInheritedSynSymbol {\n    parent_symbol_idx: Current(\n        1,\n    ),\n    modifier: Const,\n    kind: InheritedSynSymbolKind::TemplateParameter(\n        InheritedTemplateParameterSynSymbol::Type {\n            ident: `E`,\n        },\n    ),\n}\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 17,
                                    character: 40,
                                },
                                end: Position {
                                    line: 17,
                                    character: 41,
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
                97,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 96;\n\ntoken_line_group_idx = 10\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Tilde,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 19,
                                    character: 32,
                                },
                                end: Position {
                                    line: 19,
                                    character: 33,
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
                103,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 102;\n\ntoken_line_group_idx = 10\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Comma,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 19,
                                    character: 49,
                                },
                                end: Position {
                                    line: 19,
                                    character: 50,
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
                109,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 108;\n\ntoken_line_group_idx = 10\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Tilde,\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 19,
                                    character: 64,
                                },
                                end: Position {
                                    line: 19,
                                    character: 65,
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
                115,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 114;\n\ntoken_line_group_idx = 11\n\ntoken = TokenData::Ident(\n    `pop_with_largest_opt_f32`,\n);\n\ntoken_info = TokenInfo::EntityNode(\n    ItemSynNodePath::AssociatedItem(\n        AssociatedItemSynNodePath::TypeItem(\n            TypeItemSynNodePath {\n                maybe_ambiguous_path: MaybeAmbiguousPath {\n                    path: TypeItemPath {\n                        impl_block: TypeImplBlockPath {\n                            module_path: `core::vec`,\n                            ty_path: TypePath(`core::vec::Vec`, `Extern`),\n                            disambiguator: 0,\n                        },\n                        ident: `pop_with_largest_opt_f32`,\n                        item_kind: MethodFn,\n                    },\n                    disambiguator: 0,\n                },\n            },\n        ),\n    ),\n    AssociatedItem {\n        associated_item_kind: TypeItem(\n            MethodFn,\n        ),\n    },\n);\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 21,
                                    character: 11,
                                },
                                end: Position {
                                    line: 21,
                                    character: 35,
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
                121,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 120;\n\ntoken_line_group_idx = 11\n\ntoken = TokenData::Ident(\n    `f`,\n);\n\ntoken_info = TokenInfo::CurrentSymbol {\n    current_symbol_idx: 1,\n    current_symbol_kind: CurrentSynSymbolKind::ExplicitRegularParameter {\n        pattern_symbol_idx: 1,\n    },\n    syn_expr_region: ExprRegionLeash(_),\n};\n\nCurrentSynSymbol {\n    modifier: None,\n    access_start: RegionalTokenIdx(\n        10,\n    ),\n    access_end: None,\n    variant: CurrentSynSymbolVariant::ParenateRegularParameter {\n        ident: `f`,\n        pattern_symbol_idx: 1,\n    },\n}\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 21,
                                    character: 47,
                                },
                                end: Position {
                                    line: 21,
                                    character: 48,
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
                127,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 126;\n\ntoken_line_group_idx = 11\n\ntoken = TokenData::Punctuation(\n    Punctuation(\n        PunctuationMapped::Binary(\n            Curry,\n        ),\n    ),\n);\n\ntoken_info = TokenInfo::None;\n\n\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 21,
                                    character: 56,
                                },
                                end: Position {
                                    line: 21,
                                    character: 58,
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
                133,
            ),
            Some(
                HoverResult {
                    hover: Hover {
                        contents: Markup(
                            MarkupContent {
                                kind: Markdown,
                                value: "\ntoken_idx = 132;\n\ntoken_line_group_idx = 11\n\ntoken = TokenData::Ident(\n    `E`,\n);\n\ntoken_info = TokenInfo::InheritedSymbol {\n    inherited_symbol_idx: 1,\n    inherited_symbol_kind: InheritedSynSymbolKind::TemplateParameter(\n        InheritedTemplateParameterSynSymbol::Type {\n            ident: `E`,\n        },\n    ),\n    syn_expr_region: ExprRegionLeash(_),\n};\n\nInheritedSynSymbol {\n    parent_symbol_idx: Current(\n        1,\n    ),\n    modifier: Const,\n    kind: InheritedSynSymbolKind::TemplateParameter(\n        InheritedTemplateParameterSynSymbol::Type {\n            ident: `E`,\n        },\n    ),\n}\n",
                            },
                        ),
                        range: Some(
                            Range {
                                start: Position {
                                    line: 21,
                                    character: 69,
                                },
                                end: Position {
                                    line: 21,
                                    character: 70,
                                },
                            },
                        ),
                    },
                    actions: [],
                },
            ),
        ),
    ],
)