```rust
[
    (
        ItemPath(`core::result::Result`),
        Ok(
            ItemEthTemplate::MajorItem(
                MajorItemEthTemplate::Type(
                    TypeEthTemplate::Enum(
                        EnumEthTemplate {
                            path: TypePath(`core::result::Result`, `Enum`),
                            template_parameters: EthTemplateParameters {
                                data: [
                                    EthTemplateParameter {
                                        annotated_variance: None,
                                        symbol: EthSymbolicVariable(`T`),
                                        traits: [],
                                    },
                                    EthTemplateParameter {
                                        annotated_variance: None,
                                        symbol: EthSymbolicVariable(`E`),
                                        traits: [],
                                    },
                                ],
                            },
                        },
                    ),
                ),
            ),
        ),
    ),
    (
        ItemPath(`core::result::Result as core::ops::Unveil(0)`),
        Ok(
            ItemEthTemplate::ImplBlock(
                ImplBlockEthTemplate::TraitForTypeImpl(
                    TraitForTypeImplBlockEthTemplate {
                        path: TraitForTypeImplBlockPath(`core::result::Result as core::ops::Unveil(0)`),
                        template_parameters: EthTemplateParameters {
                            data: [
                                EthTemplateParameter {
                                    annotated_variance: None,
                                    symbol: EthSymbolicVariable(`T1`),
                                    traits: [],
                                },
                                EthTemplateParameter {
                                    annotated_variance: None,
                                    symbol: EthSymbolicVariable(`T2`),
                                    traits: [],
                                },
                                EthTemplateParameter {
                                    annotated_variance: None,
                                    symbol: EthSymbolicVariable(`E1`),
                                    traits: [],
                                },
                                EthTemplateParameter {
                                    annotated_variance: None,
                                    symbol: EthSymbolicVariable(`E2`),
                                    traits: [],
                                },
                            ],
                        },
                        trai: EthTerm(`Unveil Result T2 E2`),
                        self_ty_refined: PathLeading(
                            Application(
                                EthApplication(
                                    Id {
                                        value: 23,
                                    },
                                ),
                            ),
                        ),
                    },
                ),
            ),
        ),
    ),
    (
        ItemPath(`<core::result::Result as core::ops::Unveil(0)>::Continue`),
        Ok(
            ItemEthTemplate::AssocItem(
                AssocItemEthTemplate::TraitForType(
                    AssocType(
                        TraitForTypeAssocTypeEthTemplate(
                            Id {
                                value: 1,
                            },
                        ),
                    ),
                ),
            ),
        ),
    ),
    (
        ItemPath(`<core::result::Result as core::ops::Unveil(0)>::unveil`),
        Ok(
            ItemEthTemplate::AssocItem(
                AssocItemEthTemplate::TraitForType(
                    AssocRitchie(
                        TraitForTypeAssocRitchieEthTemplate(
                            Id {
                                value: 1,
                            },
                        ),
                    ),
                ),
            ),
        ),
    ),
]
```