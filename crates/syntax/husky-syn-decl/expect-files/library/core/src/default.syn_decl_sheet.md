```rust
SynDeclSheet {
    decls: [
        (
            ItemPath(`core::default::Default`),
            SynDecl::MajorItem(
                MajorItemSynDecl::Trait(
                    TraitSynDecl {
                        path: TraitPath(`core::default::Default`),
                        template_parameters: [],
                        syn_expr_region: SynExprRegion {
                            data: SynExprRegionData {
                                parent: None,
                                path: SynNodeRegionPath::ItemDecl(
                                    ItemSynNodePath::MajorItem(
                                        MajorItemSynNodePath::Trait(
                                            TraitSynNodePath(
                                                ItemSynNodePathId {
                                                    data: ItemSynNodePathData::MajorItem(
                                                        MajorItemSynNodePathData::Trait(
                                                            TraitSynNodePathData {
                                                                disambiguated_item_path: DisambiguatedItemPath {
                                                                    maybe_ambiguous_item_path: TraitPath(`core::default::Default`),
                                                                    disambiguator: 0,
                                                                },
                                                            },
                                                        ),
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                                expr_arena: Arena {
                                    data: [],
                                },
                                principal_item_path_expr_arena: Arena {
                                    data: [],
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
                                    allow_self_type: True,
                                    allow_self_value: False,
                                    pattern_ty_constraints: [],
                                },
                                pattern_roots: [],
                                expr_roots: [],
                                has_self_lifetime: false,
                                has_self_place: false,
                                pattern_to_current_variable_map: [],
                            },
                        },
                    },
                ),
            ),
        ),
    ],
}
```