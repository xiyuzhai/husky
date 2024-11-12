```rust
[
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::left_components`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::left_components`),
            ),
            place_registry: PlaceRegistry {
                infos: [],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    0,
                    (
                        SemExprIdx(
                            0,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`FermiMatchResult`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::left_coordinate_max`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::left_coordinate_max`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Parameter {
                        current_variable_idx: 0,
                        ident: `cc`,
                    },
                ],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: LeashType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        6,
                                    ),
                                    opd: SemExprIdx(
                                        0,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`core::num::f32`, `Extern`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: OptionType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    opd: SemExprIdx(
                                        2,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    1,
                    (
                        SemExprIdx(
                            1,
                        ),
                        SynExprRootKind::ExplicitParameterType,
                    ),
                ),
                (
                    3,
                    (
                        SemExprIdx(
                            3,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [
                    None,
                ],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        1,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        2,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`f32`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        3,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Option f32`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                StackPure {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::CurryDestination(
                                    ExpectCurryDestination {
                                        curry_destination: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Intact,
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsExactly(
                                    ExpectSubtypeOrEqual {
                                        expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Subtype(
                                                ExpectSubtypeOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::components_max_downwards`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::components_max_downwards`),
            ),
            place_registry: PlaceRegistry {
                infos: [],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    0,
                    (
                        SemExprIdx(
                            0,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`FermiMatchResult`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::components_max_heights`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::components_max_heights`),
            ),
            place_registry: PlaceRegistry {
                infos: [],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::fermi::FermiMatchResult`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    0,
                    (
                        SemExprIdx(
                            0,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`FermiMatchResult`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::is_four`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::is_four`),
            ),
            place_registry: PlaceRegistry {
                infos: [],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`(independent variable_ad_hoc_fmt: Type) -> independent variable_ad_hoc_fmt -> Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`(independent variable_ad_hoc_fmt: Type) -> independent variable_ad_hoc_fmt -> Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist::MnistLabel`, `Enum`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::FunctionApplication {
                                    function: SemExprIdx(
                                        0,
                                    ),
                                    argument: SemExprIdx(
                                        1,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`independent MnistLabel -> Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`independent MnistLabel -> Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 3,
                                    path: PrincipalEntityPath::TypeVariant(
                                        TypeVariantPath(`mnist::MnistLabel::Four`),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist::MnistLabel::Four`),
                                            context_itd: EthTermContextItd {
                                                task_ty: Some(
                                                    EthTerm(`MnistTask`),
                                                ),
                                            },
                                            env: TypeOntologyConstructor,
                                            variable_map: [],
                                            separator: None,
                                        },
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`MnistLabel`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`MnistLabel`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::FunctionApplication {
                                    function: SemExprIdx(
                                        2,
                                    ),
                                    argument: SemExprIdx(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    4,
                    (
                        SemExprIdx(
                            4,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        1,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`MnistLabel`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`OneVsAll`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        2,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`OneVsAll MnistLabel`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        3,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Four`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        4,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`OneVsAll MnistLabel Four`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsFunctionType(
                                    ExpectEqsFunctionType {
                                        final_destination: FinalDestination::Sort,
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`(independent variable_ad_hoc_fmt: Type) -> independent variable_ad_hoc_fmt -> Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsFunctionCallType(
                                                ExpectEqsFunctionTypeOutcome {
                                                    return_ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`independent variable_ad_hoc_fmt -> Type`),
                                                        ),
                                                    },
                                                    variant: ExpectEqsFunctionTypeOutcomeData::ExplicitCurry {
                                                        variance: Independent,
                                                        parameter_hvar: Some(
                                                            FlyHvar(
                                                                FlyTerm {
                                                                    quary: None,
                                                                    base: Eth(
                                                                        AbstractVariable(
                                                                            EthAbstractVariable(
                                                                                Id {
                                                                                    value: 1,
                                                                                },
                                                                            ),
                                                                        ),
                                                                    ),
                                                                },
                                                            ),
                                                        ),
                                                        parameter_ty: FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Eth(
                                                                EthTerm(`Type`),
                                                            ),
                                                        },
                                                        return_ty: FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Eth(
                                                                EthTerm(`independent variable_ad_hoc_fmt -> Type`),
                                                            ),
                                                        },
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::CurryDestination(
                                    ExpectCurryDestination {
                                        curry_destination: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Intact,
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsFunctionType(
                                    ExpectEqsFunctionType {
                                        final_destination: FinalDestination::Sort,
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`independent MnistLabel -> Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsFunctionCallType(
                                                ExpectEqsFunctionTypeOutcome {
                                                    return_ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`Type`),
                                                        ),
                                                    },
                                                    variant: ExpectEqsFunctionTypeOutcomeData::ExplicitCurry {
                                                        variance: Independent,
                                                        parameter_hvar: None,
                                                        parameter_ty: FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Eth(
                                                                EthTerm(`MnistLabel`),
                                                            ),
                                                        },
                                                        return_ty: FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Eth(
                                                                EthTerm(`Type`),
                                                            ),
                                                        },
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::CurryDestination(
                                    ExpectCurryDestination {
                                        curry_destination: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`MnistLabel`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`MnistLabel`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Intact,
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 4,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::displacement_downwards`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::displacement_downwards`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Parameter {
                        current_variable_idx: 0,
                        ident: `cc`,
                    },
                ],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: LeashType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        6,
                                    ),
                                    opd: SemExprIdx(
                                        0,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`core::num::f32`, `Extern`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: OptionType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    opd: SemExprIdx(
                                        2,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    1,
                    (
                        SemExprIdx(
                            1,
                        ),
                        SynExprRootKind::ExplicitParameterType,
                    ),
                ),
                (
                    3,
                    (
                        SemExprIdx(
                            3,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [
                    None,
                ],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        1,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        2,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`f32`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        3,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Option f32`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                StackPure {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::CurryDestination(
                                    ExpectCurryDestination {
                                        curry_destination: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Intact,
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsExactly(
                                    ExpectSubtypeOrEqual {
                                        expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Subtype(
                                                ExpectSubtypeOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
    SemExprRegion {
        path: RegionPath::ItemDecl(
            ItemPath(`mnist_classifier::digits::four::cc_box_heights`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDecl(
                ItemPath(`mnist_classifier::digits::four::cc_box_heights`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Parameter {
                        current_variable_idx: 0,
                        ident: `cc`,
                    },
                ],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent`, `Struct`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: LeashType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        6,
                                    ),
                                    opd: SemExprIdx(
                                        0,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Type(
                                            TypePath(`core::num::f32`, `Extern`),
                                        ),
                                    ),
                                    ty_path_disambiguation: OntologyConstructor,
                                    instantiation: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Prefix {
                                    opr: OptionType,
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    opd: SemExprIdx(
                                        2,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Type`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                ),
                            ),
                        },
                    ],
                },
            ),
            sem_stmt_arena: SemStmtArena(
                Arena {
                    data: [],
                },
            ),
            sem_expr_roots: [
                (
                    1,
                    (
                        SemExprIdx(
                            1,
                        ),
                        SynExprRootKind::ExplicitParameterType,
                    ),
                ),
                (
                    3,
                    (
                        SemExprIdx(
                            3,
                        ),
                        SynExprRootKind::ReturnType,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [
                    None,
                ],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        1,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        2,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`f32`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        3,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`Option f32`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                StackPure {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`Leash ConcaveComponent`),
                            ),
                        },
                    ),
                ],
            },
            symbol_terms: SymbolMap {
                inherited_variable_map: [],
                current_variable_map: [],
            },
            fly_term_region: FlyTermRegion {
                terms: FlyTerms {
                    sol_terms: SolTerms {
                        entries: [],
                    },
                    hol_terms: HolTerms {
                        entries: [],
                        first_unresolved_term_idx: 0,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::CurryDestination(
                                    ExpectCurryDestination {
                                        curry_destination: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Intact,
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsExactly(
                                    ExpectSubtypeOrEqual {
                                        expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Type`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Subtype(
                                                ExpectSubtypeOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::EqsSort(
                                    ExpectSort {
                                        smallest_universe: Universe(
                                            1,
                                        ),
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Type`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsSort(
                                                Universe(
                                                    1,
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            },
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: None,
            self_ty: None,
            self_value_ty: None,
            context_itd: EthTermContextItd {
                task_ty: Some(
                    EthTerm(`MnistTask`),
                ),
            },
        },
    },
]
```