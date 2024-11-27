```rust
[
    SemExprRegion {
        path: RegionPath::ItemDefn(
            ItemPath(`mnist_classifier::digits::eight::upper_mouth_match`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::digits::eight::upper_mouth_match`),
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
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::fermi::fermi_match`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::fermi::fermi_match`),
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
                                        EthTerm(`fn(( Leash Vec ConcaveComponent,  Vec fn(( Leash ConcaveComponent) -> Option f32) -> FermiMatchResult`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`fn(( Leash Vec ConcaveComponent,  Vec fn(( Leash ConcaveComponent) -> Option f32) -> FermiMatchResult`),
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
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_concave_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_concave_components`),
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
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash Vec ConcaveComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConcaveComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 2,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::digits::eight::big_mouth`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::digits::eight::big_mouth`),
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
                                        EthTerm(`fn(( Leash ConcaveComponent) -> Option f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`fn(( Leash ConcaveComponent) -> Option f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::NewList {
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                2,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    element_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`fn(( Leash ConcaveComponent) -> Option f32`),
                                        ),
                                    },
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::FunctionRitchieCall {
                                    function: SemExprIdx(
                                        0,
                                    ),
                                    ritchie_ty_kind: RitchieTypeKind::Item(
                                        RitchieItemKind::Fn,
                                    ),
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    ritchie_parameter_argument_matches: [
                                        SemRitchieArgument::Simple(
                                            FlyRitchieSimpleParameter {
                                                contract: Contract::Pure,
                                                ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Leash Vec ConcaveComponent`),
                                                    ),
                                                },
                                            },
                                            SemaSimpleArgument {
                                                argument_expr_idx: SemExprIdx(
                                                    1,
                                                ),
                                                coercion_outcome: Some(
                                                    ExpectCoercionOutcome {
                                                        coercion: Trivial(
                                                            TrivialFlyCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    },
                                                ),
                                                separator: CallListSeparator::Comma(
                                                    RegionalTokenIdx(
                                                        4,
                                                    ),
                                                ),
                                            },
                                        ),
                                        SemRitchieArgument::Simple(
                                            FlyRitchieSimpleParameter {
                                                contract: Contract::Pure,
                                                ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
                                                    ),
                                                },
                                            },
                                            SemaSimpleArgument {
                                                argument_expr_idx: SemExprIdx(
                                                    3,
                                                ),
                                                coercion_outcome: Some(
                                                    ExpectCoercionOutcome {
                                                        coercion: Trivial(
                                                            TrivialFlyCoercion {
                                                                expectee_quary: Transient,
                                                            },
                                                        ),
                                                    },
                                                ),
                                                separator: CallListSeparator::None,
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`FermiMatchResult`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`FermiMatchResult`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Block {
                                    stmts: SemStmtIdxRange(
                                        ArenaIdxRange(
                                            0..1,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`FermiMatchResult`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    5,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`FermiMatchResult`),
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
                    data: [
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Eval {
                                    expr: SemExprIdx(
                                        4,
                                    ),
                                    outcome: Some(
                                        ExpectationOutcome::Coercion(
                                            ExpectCoercionOutcome {
                                                coercion: Trivial(
                                                    TrivialFlyCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            },
                                        ),
                                    ),
                                    eol_semicolon: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`FermiMatchResult`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    5,
                    (
                        SemExprIdx(
                            5,
                        ),
                        SynExprRootKind::RootBody,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [],
            },
            sem_expr_terms: [],
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
                                        final_destination: FinalDestination::TypeOntology,
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
                                            EthTerm(`fn(( Leash Vec ConcaveComponent,  Vec fn(( Leash ConcaveComponent) -> Option f32) -> FermiMatchResult`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::EqsFunctionCallType(
                                                ExpectEqsFunctionTypeOutcome {
                                                    return_ty: FlyTerm {
                                                        quary: Some(
                                                            Transient,
                                                        ),
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`FermiMatchResult`),
                                                        ),
                                                    },
                                                    variant: ExpectEqsFunctionTypeOutcomeData::TypeRitchie {
                                                        ritchie_ty_kind: RitchieTypeKind::Item(
                                                            RitchieItemKind::Fn,
                                                        ),
                                                        parameter_contracted_tys: [
                                                            FlyRitchieParameter::Simple(
                                                                FlyRitchieSimpleParameter {
                                                                    contract: Contract::Pure,
                                                                    ty: FlyTerm {
                                                                        quary: None,
                                                                        base: FlyTermBase::Eth(
                                                                            EthTerm(`Leash Vec ConcaveComponent`),
                                                                        ),
                                                                    },
                                                                },
                                                            ),
                                                            FlyRitchieParameter::Simple(
                                                                FlyRitchieSimpleParameter {
                                                                    contract: Contract::Pure,
                                                                    ty: FlyTerm {
                                                                        quary: None,
                                                                        base: FlyTermBase::Eth(
                                                                            EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
                                                                        ),
                                                                    },
                                                                },
                                                            ),
                                                        ],
                                                    },
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Leash Vec ConcaveComponent`),
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
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConcaveComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`fn(( Leash ConcaveComponent) -> Option f32`),
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
                                            EthTerm(`fn(( Leash ConcaveComponent) -> Option f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
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
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec fn(( Leash ConcaveComponent) -> Option f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`FermiMatchResult`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 4,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`FermiMatchResult`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`FermiMatchResult`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 5,
                                    src: ExpectationSource {
                                        syn_expr_idx: 5,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`FermiMatchResult`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
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
            return_ty: Some(
                EthTerm(`FermiMatchResult`),
            ),
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
        path: RegionPath::ItemDefn(
            ItemPath(`mnist_classifier::digits::eight::is_eight`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::digits::eight::is_eight`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Variable {
                        current_variable_idx: 0,
                        ident: `upper_excess`,
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
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_connected_component`),
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
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        0,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `upper_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::upper_mass`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::upper_mass`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
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
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_connected_component`),
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
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        2,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        9,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `lower_mass`,
                                        regional_token_idx: RegionalTokenIdx(
                                            10,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::lower_mass`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::lower_mass`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Binary {
                                    lopd: SemExprIdx(
                                        1,
                                    ),
                                    opr: Closed(
                                        Sub,
                                    ),
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [],
                                            final_place: Transient,
                                        },
                                        signature: SemaBinaryOprFlySignature::Builtin,
                                    },
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    ropd: SemExprIdx(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 2,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_connected_component`),
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
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    5,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        5,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `eff_holes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            14,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash EffHoles`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash EffHoles`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    6,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        6,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            16,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Vec Option Leash RawContour`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Vec Option Leash RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    7,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec Option Leash RawContour`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        18,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            1,
                                        ),
                                    ),
                                ),
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: FlyTermBase::Hol(
                                        HolTerm(
                                            0,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    8,
                                    FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                0,
                                            ),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Index {
                                    self_argument: SemExprIdx(
                                        7,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        17,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                8,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Option Leash RawContour`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option Leash RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    10,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash RawContour`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Be {
                                    src: SemExprIdx(
                                        9,
                                    ),
                                    contract: Contract::Pure,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        20,
                                    ),
                                    target: BePatternSyndicate {
                                        pattern_root: BeSynPatternRoot {
                                            syn_pattern_idx: 1,
                                        },
                                        variables: ArenaIdxRange(
                                            1..1,
                                        ),
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    11,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 4,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::major_connected_component`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_connected_component`),
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
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    12,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        11,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        25,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `eff_holes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            26,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash EffHoles`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::eff_holes`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash EffHoles`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    13,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        12,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `matches`,
                                        regional_token_idx: RegionalTokenIdx(
                                            28,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`EffHoles`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Vec Option Leash RawContour`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Vec Option Leash RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    14,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec Option Leash RawContour`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        30,
                                    ),
                                    LiteralTokenData::Integer(
                                        UnspecifiedRegular(
                                            0,
                                        ),
                                    ),
                                ),
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: FlyTermBase::Hol(
                                        HolTerm(
                                            1,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    15,
                                    FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                1,
                                            ),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Index {
                                    self_argument: SemExprIdx(
                                        13,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        29,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                14,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        31,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Option Leash RawContour`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option Leash RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    17,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash RawContour`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Be {
                                    src: SemExprIdx(
                                        15,
                                    ),
                                    contract: Contract::Pure,
                                    be_regional_token_idx: RegionalTokenIdx(
                                        32,
                                    ),
                                    target: BePatternSyndicate {
                                        pattern_root: BeSynPatternRoot {
                                            syn_pattern_idx: 2,
                                        },
                                        variables: ArenaIdxRange(
                                            1..1,
                                        ),
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    18,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        36,
                                    ),
                                    LiteralTokenData::Bool(
                                        False,
                                    ),
                                ),
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    19,
                                    FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        38,
                                    ),
                                    LiteralTokenData::Bool(
                                        False,
                                    ),
                                ),
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    20,
                                    FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 7,
                                    path: PrincipalEntityPath::TypeVariant(
                                        TypeVariantPath(`malamute::OneVsAll::Yes`),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`malamute::OneVsAll::Yes`),
                                            context_itd: EthTermContextItd {
                                                task_ty: Some(
                                                    EthTerm(`MnistTask`),
                                                ),
                                            },
                                            env: TypeOntologyConstructor,
                                            variable_map: [
                                                (
                                                    EthSymbolicVariable(`Label`, `phan`),
                                                    FlyTermSymbolResolution::Explicit(
                                                        FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Hol(
                                                                HolTerm(
                                                                    2,
                                                                ),
                                                            ),
                                                        },
                                                    ),
                                                ),
                                                (
                                                    EthSymbolicVariable(`label`, `phan`),
                                                    FlyTermSymbolResolution::Explicit(
                                                        FlyTerm {
                                                            quary: None,
                                                            base: FlyTermBase::Hol(
                                                                HolTerm(
                                                                    3,
                                                                ),
                                                            ),
                                                        },
                                                    ),
                                                ),
                                            ],
                                            separator: None,
                                        },
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Hol(
                                        HolTerm(
                                            4,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    21,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                4,
                                            ),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Block {
                                    stmts: SemStmtIdxRange(
                                        ArenaIdxRange(
                                            3..6,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`OneVsAll MnistLabel Eight`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    24,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`OneVsAll MnistLabel Eight`),
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
                    data: [
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            35,
                                        ),
                                    },
                                    condition: Other {
                                        expr: SemExprIdx(
                                            17,
                                        ),
                                        conversion: None,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::IfElse {
                                    if_branch: SemIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                23,
                                            ),
                                        },
                                        condition: Be {
                                            expr: SemExprIdx(
                                                16,
                                            ),
                                            src: SemExprIdx(
                                                15,
                                            ),
                                            contract: Pure,
                                            be_regional_token_idx: RegionalTokenIdx(
                                                32,
                                            ),
                                            target: BePatternSyndicate {
                                                pattern_root: BeSynPatternRoot {
                                                    syn_pattern_idx: 2,
                                                },
                                                variables: ArenaIdxRange(
                                                    1..1,
                                                ),
                                            },
                                        },
                                        eol_colon_token: EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                34,
                                            ),
                                        },
                                        stmts: SemStmtIdxRange(
                                            ArenaIdxRange(
                                                0..1,
                                            ),
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            37,
                                        ),
                                    },
                                    condition: Other {
                                        expr: SemExprIdx(
                                            18,
                                        ),
                                        conversion: None,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                    },
                                    let_pattern_sem_obelisk: LetVariableObelisk {
                                        syn_pattern_root: LetPatternSynExprRoot {
                                            syn_pattern_idx: 0,
                                        },
                                        variables: ArenaIdxRange(
                                            0..1,
                                        ),
                                        colon_token: None,
                                        ty_sem_expr_idx: None,
                                    },
                                    contract: Contract::Pure,
                                    eq_token: EqRegionalToken(
                                        RegionalTokenIdx(
                                            3,
                                        ),
                                    ),
                                    initial_value: SemExprIdx(
                                        4,
                                    ),
                                    coercion_outcome: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::IfElse {
                                    if_branch: SemIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                11,
                                            ),
                                        },
                                        condition: Be {
                                            expr: SemExprIdx(
                                                10,
                                            ),
                                            src: SemExprIdx(
                                                9,
                                            ),
                                            contract: Pure,
                                            be_regional_token_idx: RegionalTokenIdx(
                                                20,
                                            ),
                                            target: BePatternSyndicate {
                                                pattern_root: BeSynPatternRoot {
                                                    syn_pattern_idx: 1,
                                                },
                                                variables: ArenaIdxRange(
                                                    1..1,
                                                ),
                                            },
                                        },
                                        eol_colon_token: EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                22,
                                            ),
                                        },
                                        stmts: SemStmtIdxRange(
                                            ArenaIdxRange(
                                                1..3,
                                            ),
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Eval {
                                    expr: SemExprIdx(
                                        19,
                                    ),
                                    outcome: Some(
                                        ExpectationOutcome::Coercion(
                                            ExpectCoercionOutcome {
                                                coercion: Trivial(
                                                    TrivialFlyCoercion {
                                                        expectee_quary: Transient,
                                                    },
                                                ),
                                            },
                                        ),
                                    ),
                                    eol_semicolon: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`OneVsAll MnistLabel Eight`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    20,
                    (
                        SemExprIdx(
                            20,
                        ),
                        SynExprRootKind::RootBody,
                    ),
                ),
            ],
            syn_pattern_ty_infos: [
                PatternTypeInfo {
                    ty: Ok(
                        FlyTerm {
                            quary: Some(
                                Transient,
                            ),
                            base: Eth(
                                ItemPath(
                                    TypeOntology(
                                        TypePath(
                                            ItemPathId(
                                                Id {
                                                    value: 139,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        },
                    ),
                },
                PatternTypeInfo {
                    ty: Ok(
                        FlyTerm {
                            quary: Some(
                                Leashed {
                                    place: None,
                                },
                            ),
                            base: Eth(
                                Application(
                                    EthApplication(
                                        Id {
                                            value: 58,
                                        },
                                    ),
                                ),
                            ),
                        },
                    ),
                },
                PatternTypeInfo {
                    ty: Ok(
                        FlyTerm {
                            quary: Some(
                                Leashed {
                                    place: None,
                                },
                            ),
                            base: Eth(
                                Application(
                                    EthApplication(
                                        Id {
                                            value: 58,
                                        },
                                    ),
                                ),
                            ),
                        },
                    ),
                },
            ],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [
                    Some(
                        PatternSymbolTypeInfo {
                            ty: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: Eth(
                                        ItemPath(
                                            TypeOntology(
                                                TypePath(
                                                    ItemPathId(
                                                        Id {
                                                            value: 139,
                                                        },
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                },
                            ),
                        },
                    ),
                ],
            },
            sem_expr_terms: [
                (
                    SemExprIdx(
                        8,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`1`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        14,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`0`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        17,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`false`),
                            ),
                        },
                    ),
                ),
                (
                    SemExprIdx(
                        18,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`false`),
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
                                ImmutableOnStack {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`f32`),
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
                        entries: [
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        8,
                                    ),
                                    hole_kind: UnspecifiedIntegerType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`usize`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::CoercibleInto {
                                            target: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`usize`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`usize`),
                                ),
                            },
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        14,
                                    ),
                                    hole_kind: UnspecifiedIntegerType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`usize`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::CoercibleInto {
                                            target: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`usize`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`usize`),
                                ),
                            },
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        19,
                                    ),
                                    hole_kind: ImplicitType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`MnistLabel`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::Subtype {
                                            target: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`MnistLabel`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`MnistLabel`),
                                ),
                            },
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        19,
                                    ),
                                    hole_kind: AnyOriginal,
                                    fill: Some(
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Eight`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::Subtype {
                                            target: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Eight`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`Eight`),
                                ),
                            },
                            HolTermEntry {
                                data: HolTermData::TypeOntology {
                                    path: TypePath(`malamute::OneVsAll`, `Enum`),
                                    refined_path: Right(
                                        OtherTypePath(
                                            TypePath(`malamute::OneVsAll`, `Enum`),
                                        ),
                                    ),
                                    arguments: [
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    2,
                                                ),
                                            ),
                                        },
                                        FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    3,
                                                ),
                                            ),
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`OneVsAll MnistLabel Eight`),
                                ),
                            },
                        ],
                        first_unresolved_term_idx: 4,
                    },
                },
                expectations: Expectations {
                    arena: Arena {
                        data: [
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                Transient,
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
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
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 4,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 5,
                                    src: ExpectationSource {
                                        syn_expr_idx: 5,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 6,
                                    src: ExpectationSource {
                                        syn_expr_idx: 6,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 7,
                                    src: ExpectationSource {
                                        syn_expr_idx: 7,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec Option Leash RawContour`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 8,
                                    src: ExpectationSource {
                                        syn_expr_idx: 8,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                0,
                                            ),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`usize`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 9,
                                    src: ExpectationSource {
                                        syn_expr_idx: 9,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                0,
                                            ),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Compterm,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 10,
                                    src: ExpectationSource {
                                        syn_expr_idx: 9,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash RawContour`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
                                ),
                                state: ExpectationState {
                                    idx: 11,
                                    src: ExpectationSource {
                                        syn_expr_idx: 10,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 12,
                                    src: ExpectationSource {
                                        syn_expr_idx: 11,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash ConnectedComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 13,
                                    src: ExpectationSource {
                                        syn_expr_idx: 12,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash EffHoles`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 14,
                                    src: ExpectationSource {
                                        syn_expr_idx: 13,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec Option Leash RawContour`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 15,
                                    src: ExpectationSource {
                                        syn_expr_idx: 14,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                1,
                                            ),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`usize`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 16,
                                    src: ExpectationSource {
                                        syn_expr_idx: 15,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                1,
                                            ),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Compterm,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 17,
                                    src: ExpectationSource {
                                        syn_expr_idx: 15,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash RawContour`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
                                ),
                                state: ExpectationState {
                                    idx: 18,
                                    src: ExpectationSource {
                                        syn_expr_idx: 16,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
                                ),
                                state: ExpectationState {
                                    idx: 19,
                                    src: ExpectationSource {
                                        syn_expr_idx: 17,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
                                ),
                                state: ExpectationState {
                                    idx: 20,
                                    src: ExpectationSource {
                                        syn_expr_idx: 18,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`OneVsAll MnistLabel Eight`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 21,
                                    src: ExpectationSource {
                                        syn_expr_idx: 19,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                4,
                                            ),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
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
                                                EthTerm(`MnistLabel`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 22,
                                    src: ExpectationSource {
                                        syn_expr_idx: 19,
                                        kind: Expectation(
                                            21,
                                        ),
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                2,
                                            ),
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
                                expectation: Expectation::EqsExactly(
                                    ExpectSubtypeOrEqual {
                                        expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Eight`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 23,
                                    src: ExpectationSource {
                                        syn_expr_idx: 19,
                                        kind: Expectation(
                                            21,
                                        ),
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Hol(
                                            HolTerm(
                                                3,
                                            ),
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`OneVsAll MnistLabel Eight`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 24,
                                    src: ExpectationSource {
                                        syn_expr_idx: 20,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`OneVsAll MnistLabel Eight`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
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
            return_ty: Some(
                EthTerm(`OneVsAll MnistLabel Eight`),
            ),
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
        path: RegionPath::ItemDefn(
            ItemPath(`mnist_classifier::digits::eight::big_mouth`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::digits::eight::big_mouth`),
            ),
            place_registry: PlaceRegistry {
                infos: [],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                            ),
                            ty_result: Ok(
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
                            expectation_idx_and_ty: Some(
                                (
                                    0,
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
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        0,
                                    ),
                                    self_argument_ty: FlyTerm {
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
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        3,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `relative_bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            4,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: StackPure {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`RelativeBoundingBox`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`RelativeBoundingBox`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash RelativeBoundingBox`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::relative_bounding_box`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::relative_bounding_box`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash RelativeBoundingBox`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RelativeBoundingBox`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::MethodRitchieCall {
                                    self_argument: SemExprIdx(
                                        1,
                                    ),
                                    self_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`RelativeBoundingBox`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        5,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymax`,
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: MethodFlySignature::TypeMethodRitchie(
                                            TypeMethodRitchieFlySignature {
                                                path: TypeItemPath(
                                                    `mnist_classifier::geom2d::RelativeBoundingBox(0)::ymax`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`RelativeBoundingBox`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`RelativeBoundingBox`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`f32`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`mnist_classifier::geom2d::RelativeBoundingBox(0)::ymax`),
                                                    context_itd: EthTermContextItd {
                                                        task_ty: Some(
                                                            EthTerm(`MnistTask`),
                                                        ),
                                                    },
                                                    env: MethodFn {
                                                        self_place: Leashed {
                                                            place: None,
                                                        },
                                                    },
                                                    variable_map: [],
                                                    separator: Some(
                                                        0,
                                                    ),
                                                },
                                            },
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        8,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        10,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 29,
                                                },
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Binary {
                                    lopd: SemExprIdx(
                                        2,
                                    ),
                                    opr: Comparison(
                                        Greater,
                                    ),
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [],
                                            final_place: Transient,
                                        },
                                        signature: SemaBinaryOprFlySignature::Builtin,
                                    },
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        9,
                                    ),
                                    ropd: SemExprIdx(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                            ),
                            ty_result: Ok(
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
                            expectation_idx_and_ty: Some(
                                (
                                    5,
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
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        5,
                                    ),
                                    self_argument_ty: FlyTerm {
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
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        14,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            15,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: StackPure {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`ConcaveComponent`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    6,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::MethodRitchieCall {
                                    self_argument: SemExprIdx(
                                        6,
                                    ),
                                    self_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        16,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `first`,
                                        regional_token_idx: RegionalTokenIdx(
                                            17,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: MethodFlySignature::TypeMethodRitchie(
                                            TypeMethodRitchieFlySignature {
                                                path: TypeItemPath(
                                                    `core::slice::CyclicSlice(0)::first`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`CyclicSlice LineSegmentStroke`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`CyclicSlice LineSegmentStroke`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Option Leash LineSegmentStroke`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`core::slice::CyclicSlice(0)::first`),
                                                    context_itd: EthTermContextItd {
                                                        task_ty: Some(
                                                            EthTerm(`MnistTask`),
                                                        ),
                                                    },
                                                    env: MethodFn {
                                                        self_place: Leashed {
                                                            place: None,
                                                        },
                                                    },
                                                    variable_map: [
                                                        (
                                                            EthSymbolicVariable(`E`, `mono`),
                                                            FlyTermSymbolResolution::Explicit(
                                                                FlyTerm {
                                                                    quary: None,
                                                                    base: FlyTermBase::Eth(
                                                                        EthTerm(`LineSegmentStroke`),
                                                                    ),
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    separator: Some(
                                                        1,
                                                    ),
                                                },
                                            },
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        18,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option Leash LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    7,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Unwrap {
                                    opd: SemExprIdx(
                                        7,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        20,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    8,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        8,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        21,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `start`,
                                        regional_token_idx: RegionalTokenIdx(
                                            22,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`LineSegmentStroke`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Point2d`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Point2d`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    9,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        9,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        23,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `x`,
                                        regional_token_idx: RegionalTokenIdx(
                                            24,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Point2d`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    10,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        26,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                            ),
                            ty_result: Ok(
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
                            expectation_idx_and_ty: Some(
                                (
                                    11,
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
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        11,
                                    ),
                                    self_argument_ty: FlyTerm {
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
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `strokes`,
                                        regional_token_idx: RegionalTokenIdx(
                                            28,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: StackPure {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`ConcaveComponent`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    12,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::MethodRitchieCall {
                                    self_argument: SemExprIdx(
                                        12,
                                    ),
                                    self_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        29,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `first`,
                                        regional_token_idx: RegionalTokenIdx(
                                            30,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: MethodFlySignature::TypeMethodRitchie(
                                            TypeMethodRitchieFlySignature {
                                                path: TypeItemPath(
                                                    `core::slice::CyclicSlice(0)::first`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`CyclicSlice LineSegmentStroke`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`CyclicSlice LineSegmentStroke`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Option Leash LineSegmentStroke`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`core::slice::CyclicSlice(0)::first`),
                                                    context_itd: EthTermContextItd {
                                                        task_ty: Some(
                                                            EthTerm(`MnistTask`),
                                                        ),
                                                    },
                                                    env: MethodFn {
                                                        self_place: Leashed {
                                                            place: None,
                                                        },
                                                    },
                                                    variable_map: [
                                                        (
                                                            EthSymbolicVariable(`E`, `mono`),
                                                            FlyTermSymbolResolution::Explicit(
                                                                FlyTerm {
                                                                    quary: None,
                                                                    base: FlyTermBase::Eth(
                                                                        EthTerm(`LineSegmentStroke`),
                                                                    ),
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                    separator: Some(
                                                        1,
                                                    ),
                                                },
                                            },
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        31,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        32,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option Leash LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    13,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Unwrap {
                                    opd: SemExprIdx(
                                        13,
                                    ),
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        33,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash LineSegmentStroke`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    14,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        14,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        34,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `end`,
                                        regional_token_idx: RegionalTokenIdx(
                                            35,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`LineSegmentStroke`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Point2d`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Point2d`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    15,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        15,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        36,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `x`,
                                        regional_token_idx: RegionalTokenIdx(
                                            37,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Leashed {
                                                place: None,
                                            },
                                            indirections: [],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::PropsStruct {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Point2d`),
                                                ),
                                            },
                                            ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Leashed {
                                            place: None,
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    16,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Binary {
                                    lopd: SemExprIdx(
                                        10,
                                    ),
                                    opr: Comparison(
                                        Greater,
                                    ),
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [],
                                            final_place: Transient,
                                        },
                                        signature: SemaBinaryOprFlySignature::Builtin,
                                    },
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        25,
                                    ),
                                    ropd: SemExprIdx(
                                        16,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`bool`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    17,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::InheritedVariable {
                                    ident: `cc`,
                                    regional_token_idx: RegionalTokenIdx(
                                        38,
                                    ),
                                    inherited_variable_idx: 0,
                                    inherited_variable_kind: InheritedVariableKind::Parenate {
                                        ident: `cc`,
                                    },
                                },
                            ),
                            ty_result: Ok(
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
                            expectation_idx_and_ty: Some(
                                (
                                    18,
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
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        18,
                                    ),
                                    self_argument_ty: FlyTerm {
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
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        39,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `relative_bounding_box`,
                                        regional_token_idx: RegionalTokenIdx(
                                            40,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: StackPure {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FieldFlySignature::Memoized {
                                            self_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`RelativeBoundingBox`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`RelativeBoundingBox`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash RelativeBoundingBox`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::relative_bounding_box`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::line_segment_sketch::concave_component::ConcaveComponent(0)::relative_bounding_box`),
                                                context_itd: EthTermContextItd {
                                                    task_ty: Some(
                                                        EthTerm(`MnistTask`),
                                                    ),
                                                },
                                                env: MemoizedField,
                                                variable_map: [],
                                                separator: Some(
                                                    0,
                                                ),
                                            },
                                        },
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Leash RelativeBoundingBox`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    19,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RelativeBoundingBox`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::MethodRitchieCall {
                                    self_argument: SemExprIdx(
                                        19,
                                    ),
                                    self_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`RelativeBoundingBox`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        41,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ymax`,
                                        regional_token_idx: RegionalTokenIdx(
                                            42,
                                        ),
                                    },
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: MethodFlySignature::TypeMethodRitchie(
                                            TypeMethodRitchieFlySignature {
                                                path: TypeItemPath(
                                                    `mnist_classifier::geom2d::RelativeBoundingBox(0)::ymax`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`RelativeBoundingBox`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`RelativeBoundingBox`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`f32`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`mnist_classifier::geom2d::RelativeBoundingBox(0)::ymax`),
                                                    context_itd: EthTermContextItd {
                                                        task_ty: Some(
                                                            EthTerm(`MnistTask`),
                                                        ),
                                                    },
                                                    env: MethodFn {
                                                        self_place: Leashed {
                                                            place: None,
                                                        },
                                                    },
                                                    variable_map: [],
                                                    separator: Some(
                                                        0,
                                                    ),
                                                },
                                            },
                                        ),
                                    },
                                    template_arguments: None,
                                    lpar_regional_token_idx: RegionalTokenIdx(
                                        43,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        44,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    20,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Block {
                                    stmts: SemStmtIdxRange(
                                        ArenaIdxRange(
                                            1..3,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    21,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option f32`),
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
                    data: [
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Require {
                                    require_token: RequireRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                    },
                                    condition: Other {
                                        expr: SemExprIdx(
                                            17,
                                        ),
                                        conversion: None,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::IfElse {
                                    if_branch: SemIfBranch {
                                        if_token: IfRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                1,
                                            ),
                                        },
                                        condition: Other {
                                            expr: SemExprIdx(
                                                4,
                                            ),
                                            conversion: None,
                                        },
                                        eol_colon_token: EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                11,
                                            ),
                                        },
                                        stmts: SemStmtIdxRange(
                                            ArenaIdxRange(
                                                0..1,
                                            ),
                                        ),
                                    },
                                    elif_branches: [],
                                    else_branch: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Eval {
                                    expr: SemExprIdx(
                                        20,
                                    ),
                                    outcome: Some(
                                        ExpectationOutcome::Coercion(
                                            ExpectCoercionOutcome {
                                                coercion: WrapInSome,
                                            },
                                        ),
                                    ),
                                    eol_semicolon: None,
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Option f32`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    21,
                    (
                        SemExprIdx(
                            21,
                        ),
                        SynExprRootKind::RootBody,
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
                        3,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`0.5f32`),
                            ),
                        },
                    ),
                ),
            ],
            symbol_tys: SymbolMap {
                inherited_variable_map: [
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
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 0,
                                    src: ExpectationSource {
                                        syn_expr_idx: 0,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
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
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 1,
                                    src: ExpectationSource {
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RelativeBoundingBox`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 2,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                Transient,
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
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
                                        quary: Some(
                                            Compterm,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Compterm,
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
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
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 5,
                                    src: ExpectationSource {
                                        syn_expr_idx: 5,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
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
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 6,
                                    src: ExpectationSource {
                                        syn_expr_idx: 6,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 7,
                                    src: ExpectationSource {
                                        syn_expr_idx: 7,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 8,
                                    src: ExpectationSource {
                                        syn_expr_idx: 8,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 9,
                                    src: ExpectationSource {
                                        syn_expr_idx: 9,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 10,
                                    src: ExpectationSource {
                                        syn_expr_idx: 15,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 11,
                                    src: ExpectationSource {
                                        syn_expr_idx: 10,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
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
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 12,
                                    src: ExpectationSource {
                                        syn_expr_idx: 11,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash CyclicSlice LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 13,
                                    src: ExpectationSource {
                                        syn_expr_idx: 12,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option Leash LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 14,
                                    src: ExpectationSource {
                                        syn_expr_idx: 13,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentStroke`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 15,
                                    src: ExpectationSource {
                                        syn_expr_idx: 14,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Point2d`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                Leashed {
                                                    place: None,
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 16,
                                    src: ExpectationSource {
                                        syn_expr_idx: 16,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Leashed {
                                                                place: None,
                                                            },
                                                        },
                                                    ),
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::ConditionType(
                                    ExpectConditionType,
                                ),
                                state: ExpectationState {
                                    idx: 17,
                                    src: ExpectationSource {
                                        syn_expr_idx: 17,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`bool`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::ConditionType(
                                                ExpectConditionTypeOutcome {
                                                    conversion: None,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 18,
                                    src: ExpectationSource {
                                        syn_expr_idx: 18,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
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
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 19,
                                    src: ExpectationSource {
                                        syn_expr_idx: 19,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RelativeBoundingBox`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::AnyOriginal(
                                                ExpectAnyOriginalOutcome,
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Option f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 20,
                                    src: ExpectationSource {
                                        syn_expr_idx: 20,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: WrapInSome,
                                                },
                                            ),
                                        ),
                                    ),
                                },
                            },
                            FlyTermExpectationEntry {
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Option f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 21,
                                    src: ExpectationSource {
                                        syn_expr_idx: 21,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Option f32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: Transient,
                                                        },
                                                    ),
                                                },
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
            return_ty: Some(
                EthTerm(`Option f32`),
            ),
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