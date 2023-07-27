Ok(
    EntitySynTreePresheet {
        module_path: `std`,
        major_entity_node_table: MajorEntityNodeTable {
            entries: [
                EntityNodeEntry {
                    node: EntitySynNode::Submodule(
                        SubmoduleSynNode {
                            syn_node_path: SubmoduleSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: `std::prelude`,
                                    disambiguator: 0,
                                },
                            },
                            visibility: Scope::PubUnder(
                                `std`,
                            ),
                            ast_idx: 0,
                            ident_token: IdentToken {
                                ident: `prelude`,
                                token_idx: TokenIdx(
                                    1,
                                ),
                            },
                        },
                    ),
                    syn_node_path: EntitySynNodePath::Submodule(
                        SubmoduleSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: `std::prelude`,
                                disambiguator: 0,
                            },
                        },
                    ),
                    ident: `prelude`,
                    visibility: Scope::PubUnder(
                        `std`,
                    ),
                },
                EntityNodeEntry {
                    node: EntitySynNode::Submodule(
                        SubmoduleSynNode {
                            syn_node_path: SubmoduleSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: `std::logic`,
                                    disambiguator: 0,
                                },
                            },
                            visibility: Scope::PubUnder(
                                `std`,
                            ),
                            ast_idx: 1,
                            ident_token: IdentToken {
                                ident: `logic`,
                                token_idx: TokenIdx(
                                    3,
                                ),
                            },
                        },
                    ),
                    syn_node_path: EntitySynNodePath::Submodule(
                        SubmoduleSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: `std::logic`,
                                disambiguator: 0,
                            },
                        },
                    ),
                    ident: `logic`,
                    visibility: Scope::PubUnder(
                        `std`,
                    ),
                },
                EntityNodeEntry {
                    node: EntitySynNode::Submodule(
                        SubmoduleSynNode {
                            syn_node_path: SubmoduleSynNodePath {
                                maybe_ambiguous_path: MaybeAmbiguousPath {
                                    path: `std::ops`,
                                    disambiguator: 0,
                                },
                            },
                            visibility: Scope::PubUnder(
                                `std`,
                            ),
                            ast_idx: 2,
                            ident_token: IdentToken {
                                ident: `ops`,
                                token_idx: TokenIdx(
                                    5,
                                ),
                            },
                        },
                    ),
                    syn_node_path: EntitySynNodePath::Submodule(
                        SubmoduleSynNodePath {
                            maybe_ambiguous_path: MaybeAmbiguousPath {
                                path: `std::ops`,
                                disambiguator: 0,
                            },
                        },
                    ),
                    ident: `ops`,
                    visibility: Scope::PubUnder(
                        `std`,
                    ),
                },
            ],
        },
        use_one_trackers: OnceUseRules(
            [],
        ),
        use_all_trackers: UseAllModuleSymbolsRules(
            [],
        ),
        use_expr_arena: Arena {
            data: [],
        },
        errors: [],
    },
)