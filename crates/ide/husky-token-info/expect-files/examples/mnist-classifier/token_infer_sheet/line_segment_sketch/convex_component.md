Ok(
    TokenInfoSheet {
        token_infos: [
            TokenInfo::None,
            TokenInfo::UseExpr {
                use_expr_idx: 2,
                rule_idx: UseExprRuleIdx(
                    0,
                ),
                state: UseExprRuleState::Resolved {
                    original_symbol: EntitySymbol::CrateRoot {
                        root_module_path: `mnist_classifier`,
                    },
                },
            },
            TokenInfo::None,
            TokenInfo::UseExpr {
                use_expr_idx: 1,
                rule_idx: UseExprRuleIdx(
                    1,
                ),
                state: UseExprRuleState::Resolved {
                    original_symbol: EntitySymbol::Submodule(
                        SubmoduleSymbol {
                            path: `mnist_classifier::line_segment_sketch`,
                            visibility: Scope::PubUnder(
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
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Type(
                            TypePath(`mnist_classifier::line_segment_sketch::convex_component::ConvexComponent`, `Struct`),
                        ),
                    ),
                ),
                Some(
                    ModuleItem {
                        module_item_kind: Type(
                            Struct,
                        ),
                        connection: Connected,
                    },
                ),
            ),
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Type(
                            TypePath(`mnist_classifier::line_segment_sketch::LineSegmentSketch`, `Struct`),
                        ),
                    ),
                ),
                None,
            ),
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::BoxPrefix,
            TokenInfo::None,
            TokenInfo::BoxPrefix,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Type(
                            TypePath(`mnist_classifier::line_segment_sketch::LineSegmentStroke`, `Struct`),
                        ),
                    ),
                ),
                None,
            ),
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Trait(
                            TraitPath(`core::visual::Visualize`),
                        ),
                    ),
                ),
                None,
            ),
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Type(
                            TypePath(`mnist_classifier::line_segment_sketch::convex_component::ConvexComponent`, `Struct`),
                        ),
                    ),
                ),
                None,
            ),
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::AssociatedItem(
                        AssociatedItemPath::TraitForTypeItem(
                            TraitForTypeItemPath {
                                parent_ty: TypePath(`mnist_classifier::line_segment_sketch::convex_component::ConvexComponent`, `Struct`),
                                trai: TraitPath(`core::visual::Visualize`),
                                ident: `visualize`,
                                item_kind: MethodFn,
                            },
                        ),
                    ),
                ),
                Some(
                    AssociatedItem {
                        associated_item_kind: TraitForTypeItem(
                            MethodFn,
                        ),
                    },
                ),
            ),
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::None,
            TokenInfo::Entity(
                Some(
                    EntityPath::ModuleItem(
                        ModuleItemPath::Type(
                            TypePath(`core::visual::Html`, `Extern`),
                        ),
                    ),
                ),
                None,
            ),
            TokenInfo::None,
            TokenInfo::SelfValue,
            TokenInfo::None,
            TokenInfo::Field,
            TokenInfo::None,
            TokenInfo::Method,
            TokenInfo::None,
            TokenInfo::None,
        ],
    },
)