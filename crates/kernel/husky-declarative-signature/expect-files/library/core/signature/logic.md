[
    Ok(
        Signature::Type(
            TypeDeclarativeSignatureTemplate::Extern(
                ExternDeclarativeSignatureTemplate {
                    implicit_parameters: ImplicitParameterDeclarativeSignatures {
                        data: [],
                    },
                },
            ),
        ),
    ),
    Ok(
        Signature::Type(
            TypeDeclarativeSignatureTemplate::Structure(
                StructureDeclarativeSignatureTemplate {
                    implicit_parameters: ImplicitParameterDeclarativeSignatures {
                        data: [
                            ImplicitParameterDeclarativeSignature {
                                annotated_variance: None,
                                symbol: DeclarativeTermSymbol(
                                    Id {
                                        value: 1,
                                    },
                                ),
                                traits: [],
                            },
                            ImplicitParameterDeclarativeSignature {
                                annotated_variance: None,
                                symbol: DeclarativeTermSymbol(
                                    Id {
                                        value: 3,
                                    },
                                ),
                                traits: [],
                            },
                        ],
                    },
                },
            ),
        ),
    ),
    Ok(
        Signature::Type(
            TypeDeclarativeSignatureTemplate::Inductive(
                InductiveDeclarativeSignatureTemplate {
                    implicit_parameters: ImplicitParameterDeclarativeSignatures {
                        data: [
                            ImplicitParameterDeclarativeSignature {
                                annotated_variance: None,
                                symbol: DeclarativeTermSymbol(
                                    Id {
                                        value: 1,
                                    },
                                ),
                                traits: [],
                            },
                            ImplicitParameterDeclarativeSignature {
                                annotated_variance: None,
                                symbol: DeclarativeTermSymbol(
                                    Id {
                                        value: 3,
                                    },
                                ),
                                traits: [],
                            },
                        ],
                    },
                },
            ),
        ),
    ),
]