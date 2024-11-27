```rust
[
    SemExprRegion {
        path: RegionPath::ItemDefn(
            ItemPath(`mnist_classifier::major::connected_components`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::connected_components`),
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
                                            MajorFormPath(`mnist_classifier::connected_component::find_connected_components`, `Ritchie(
                                                Fn,
                                            )`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::connected_component::find_connected_components`),
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
                                        EthTerm(`fn(( BinaryImage28) -> Vec ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`fn(( BinaryImage28) -> Vec ConnectedComponent`),
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
                                            MajorFormPath(`mnist::INPUT`, `StaticVar`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist::INPUT`),
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
                                        EthTerm(`Leash BinaryImage28`),
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
                                            EthTerm(`Leash BinaryImage28`),
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
                                                        EthTerm(`BinaryImage28`),
                                                    ),
                                                },
                                            },
                                            SemaSimpleArgument {
                                                argument_expr_idx: SemExprIdx(
                                                    1,
                                                ),
                                                coercion_outcome: Some(
                                                    ExpectCoercionOutcome {
                                                        coercion: Dedirection(
                                                            Deleash,
                                                        ),
                                                    },
                                                ),
                                                separator: CallListSeparator::None,
                                            },
                                        ),
                                    ],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`Vec ConnectedComponent`),
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
                                            EthTerm(`Vec ConnectedComponent`),
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
                                        EthTerm(`Vec ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec ConnectedComponent`),
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
                                        2,
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
                                        EthTerm(`Vec ConnectedComponent`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    3,
                    (
                        SemExprIdx(
                            3,
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
                                            EthTerm(`fn(( BinaryImage28) -> Vec ConnectedComponent`),
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
                                                            EthTerm(`Vec ConnectedComponent`),
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
                                                                            EthTerm(`BinaryImage28`),
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
                                                EthTerm(`BinaryImage28`),
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
                                            EthTerm(`Leash BinaryImage28`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Dedirection(
                                                        Deleash,
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
                                                EthTerm(`Vec ConnectedComponent`),
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
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec ConnectedComponent`),
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
                                                EthTerm(`Vec ConnectedComponent`),
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
                                            EthTerm(`Vec ConnectedComponent`),
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
                EthTerm(`Vec ConnectedComponent`),
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
            ItemPath(`mnist_classifier::major::major_connected_component`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::major_connected_component`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Variable {
                        current_variable_idx: 0,
                        ident: `i0`,
                    },
                    PlaceInfo::Variable {
                        current_variable_idx: 1,
                        ident: `max_row_span_sum`,
                    },
                    PlaceInfo::Variable {
                        current_variable_idx: 2,
                        ident: `i`,
                    },
                    PlaceInfo::Variable {
                        current_variable_idx: 3,
                        ident: `row_span_sum`,
                    },
                ],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        5,
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
                                            0,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
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
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        10,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
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
                                    base: FlyTermBase::Hol(
                                        HolTerm(
                                            1,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    1,
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
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::connected_components`),
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
                                        EthTerm(`Leash Vec ConnectedComponent`),
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::MethodRitchieCall {
                                    self_argument: SemExprIdx(
                                        2,
                                    ),
                                    self_ty: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Vec ConnectedComponent`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ilen`,
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
                                        signature: MethodFlySignature::TypeMethodRitchie(
                                            TypeMethodRitchieFlySignature {
                                                path: TypeItemPath(
                                                    `core::vec::Vec(0)::ilen`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`Vec ConnectedComponent`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Vec ConnectedComponent`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`i32`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`core::vec::Vec(0)::ilen`),
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
                                                                        EthTerm(`ConnectedComponent`),
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
                                        17,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        18,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
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
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::FrameVarDecl {
                                    regional_token_idx: RegionalTokenIdx(
                                        12,
                                    ),
                                    ident: `i`,
                                    for_loop_varible_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(2),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
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
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::connected_components`),
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
                                        EthTerm(`Leash Vec ConnectedComponent`),
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `i`,
                                    regional_token_idx: RegionalTokenIdx(
                                        25,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(2),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    6,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Index {
                                    self_argument: SemExprIdx(
                                        5,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        24,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                6,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        26,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`ConnectedComponent`),
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
                                        EthTerm(`ConnectedComponent`),
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
                                            EthTerm(`ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        7,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `row_span_sum`,
                                        regional_token_idx: RegionalTokenIdx(
                                            28,
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
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`),
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
                                    8,
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
                                SemExprData::CurrentVariable {
                                    ident: `row_span_sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        30,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(3),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    9,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(3),
                                                ),
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
                                SemExprData::CurrentVariable {
                                    ident: `max_row_span_sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        32,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(1),
                                            ),
                                        },
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
                                    10,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
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
                                SemExprData::Binary {
                                    lopd: SemExprIdx(
                                        9,
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
                                        31,
                                    ),
                                    ropd: SemExprIdx(
                                        10,
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
                                SemExprData::CurrentVariable {
                                    ident: `max_row_span_sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        34,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 1,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(1),
                                            ),
                                        },
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
                                    12,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
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
                                SemExprData::CurrentVariable {
                                    ident: `row_span_sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        36,
                                    ),
                                    current_variable_idx: 3,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 2,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(3),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`f32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    13,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(3),
                                                ),
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
                                        12,
                                    ),
                                    opr: Assign,
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [],
                                            final_place: Transient,
                                        },
                                        signature: SemaBinaryOprFlySignature::Builtin,
                                    },
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        35,
                                    ),
                                    ropd: SemExprIdx(
                                        13,
                                    ),
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
                            expectation_idx_and_ty: Some(
                                (
                                    14,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `i0`,
                                    regional_token_idx: RegionalTokenIdx(
                                        37,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(0),
                                            ),
                                        },
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
                                    15,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                SemExprData::CurrentVariable {
                                    ident: `i`,
                                    regional_token_idx: RegionalTokenIdx(
                                        39,
                                    ),
                                    current_variable_idx: 2,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        3,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(2),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    16,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Binary {
                                    lopd: SemExprIdx(
                                        15,
                                    ),
                                    opr: Assign,
                                    dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [],
                                            final_place: Transient,
                                        },
                                        signature: SemaBinaryOprFlySignature::Builtin,
                                    },
                                    opr_regional_token_idx: RegionalTokenIdx(
                                        38,
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
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    17,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
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
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::connected_components`),
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
                                        EthTerm(`Leash Vec ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    18,
                                    FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `i0`,
                                    regional_token_idx: RegionalTokenIdx(
                                        43,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(0),
                                            ),
                                        },
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
                                    19,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                        18,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        42,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                19,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        44,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`ConnectedComponent`),
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
                                        EthTerm(`ConnectedComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    20,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`ConnectedComponent`),
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
                                            4..8,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`never`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    21,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`never`),
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
                                        14,
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
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Eval {
                                    expr: SemExprIdx(
                                        17,
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
                                            20,
                                        ),
                                    },
                                    let_pattern_sem_obelisk: LetVariableObelisk {
                                        syn_pattern_root: LetPatternSynExprRoot {
                                            syn_pattern_idx: 2,
                                        },
                                        variables: ArenaIdxRange(
                                            3..4,
                                        ),
                                        colon_token: None,
                                        ty_sem_expr_idx: None,
                                    },
                                    contract: Contract::Pure,
                                    eq_token: EqRegionalToken(
                                        RegionalTokenIdx(
                                            22,
                                        ),
                                    ),
                                    initial_value: SemExprIdx(
                                        8,
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
                                                29,
                                            ),
                                        },
                                        condition: Other {
                                            expr: SemExprIdx(
                                                11,
                                            ),
                                            conversion: None,
                                        },
                                        eol_colon_token: EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                33,
                                            ),
                                        },
                                        stmts: SemStmtIdxRange(
                                            ArenaIdxRange(
                                                0..2,
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
                                    contract: Contract::Move,
                                    eq_token: EqRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    initial_value: SemExprIdx(
                                        0,
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
                                SemStmtData::Let {
                                    let_token: LetRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    let_pattern_sem_obelisk: LetVariableObelisk {
                                        syn_pattern_root: LetPatternSynExprRoot {
                                            syn_pattern_idx: 1,
                                        },
                                        variables: ArenaIdxRange(
                                            1..2,
                                        ),
                                        colon_token: None,
                                        ty_sem_expr_idx: None,
                                    },
                                    contract: Contract::Move,
                                    eq_token: EqRegionalToken(
                                        RegionalTokenIdx(
                                            9,
                                        ),
                                    ),
                                    initial_value: SemExprIdx(
                                        1,
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
                                SemStmtData::ForBetween {
                                    for_token: StmtForRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            11,
                                        ),
                                    },
                                    particulars: SemForBetweenParticulars {
                                        for_between_loop_var_regional_token_idx: RegionalTokenIdx(
                                            12,
                                        ),
                                        for_between_loop_var_ident: `i`,
                                        for_between_loop_var_expr_idx: SemExprIdx(
                                            4,
                                        ),
                                        range: SemaForBetweenRange {
                                            initial_boundary: SemaForBetweenLoopBoundary {
                                                bound_expr: None,
                                                kind: LowerClosed,
                                            },
                                            final_boundary: SemaForBetweenLoopBoundary {
                                                bound_expr: Some(
                                                    SemExprIdx(
                                                        3,
                                                    ),
                                                ),
                                                kind: UpperOpen,
                                            },
                                            step: Constant(
                                                1,
                                            ),
                                        },
                                    },
                                    for_loop_varible_idx: 2,
                                    eol_colon: EolRegionalToken::Colon(
                                        EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                19,
                                            ),
                                        },
                                    ),
                                    stmts: SemStmtIdxRange(
                                        ArenaIdxRange(
                                            2..4,
                                        ),
                                    ),
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
                                SemStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            40,
                                        ),
                                    },
                                    result: SemExprIdx(
                                        20,
                                    ),
                                    coercion_outcome: Some(
                                        ExpectCoercionOutcome {
                                            coercion: Redirection(
                                                Releash,
                                            ),
                                        },
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`never`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    22,
                    (
                        SemExprIdx(
                            21,
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
                                Compterm,
                            ),
                            base: Hol(
                                HolTerm(
                                    0,
                                ),
                            ),
                        },
                    ),
                },
                PatternTypeInfo {
                    ty: Ok(
                        FlyTerm {
                            quary: Some(
                                Compterm,
                            ),
                            base: Hol(
                                HolTerm(
                                    1,
                                ),
                            ),
                        },
                    ),
                },
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
            ],
            syn_pattern_variable_ty_infos: ArenaMap {
                data: [
                    Some(
                        PatternSymbolTypeInfo {
                            ty: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: Hol(
                                        HolTerm(
                                            0,
                                        ),
                                    ),
                                },
                            ),
                        },
                    ),
                    Some(
                        PatternSymbolTypeInfo {
                            ty: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Compterm,
                                    ),
                                    base: Hol(
                                        HolTerm(
                                            1,
                                        ),
                                    ),
                                },
                            ),
                        },
                    ),
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
                        0,
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
                        1,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`0.0f32`),
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
                                MutableOnStack {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Hol(
                                HolTerm(
                                    0,
                                ),
                            ),
                        },
                    ),
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                MutableOnStack {
                                    place: Idx(
                                        PlaceIdx(1),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Hol(
                                HolTerm(
                                    1,
                                ),
                            ),
                        },
                    ),
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                ImmutableOnStack {
                                    place: Idx(
                                        PlaceIdx(2),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`i32`),
                            ),
                        },
                    ),
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                ImmutableOnStack {
                                    place: Idx(
                                        PlaceIdx(3),
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
                                        0,
                                    ),
                                    hole_kind: UnspecifiedIntegerType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: Some(
                                                ImmutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(2),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`i32`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::CoercibleFrom {
                                            target: FlyTerm {
                                                quary: Some(
                                                    ImmutableOnStack {
                                                        place: Idx(
                                                            PlaceIdx(2),
                                                        ),
                                                    },
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`i32`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`i32`),
                                ),
                            },
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        1,
                                    ),
                                    hole_kind: UnspecifiedFloatType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: Some(
                                                ImmutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(3),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::CoercibleInto {
                                            target: FlyTerm {
                                                quary: Some(
                                                    ImmutableOnStack {
                                                        place: Idx(
                                                            PlaceIdx(3),
                                                        ),
                                                    },
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`f32`),
                                ),
                            },
                        ],
                        first_unresolved_term_idx: 2,
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 4,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
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
                                                ImmutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(2),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`i32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: ImmutableOnStack {
                                                                place: Idx(
                                                                    PlaceIdx(2),
                                                                ),
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
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 5,
                                    src: ExpectationSource {
                                        syn_expr_idx: 6,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                        syn_expr_idx: 7,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
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
                                        syn_expr_idx: 8,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`ConnectedComponent`),
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
                                        syn_expr_idx: 9,
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
                                    idx: 9,
                                    src: ExpectationSource {
                                        syn_expr_idx: 10,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(3),
                                                ),
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                ImmutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(3),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 10,
                                    src: ExpectationSource {
                                        syn_expr_idx: 11,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
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
                                                            expectee_quary: MutableOnStack {
                                                                place: Idx(
                                                                    PlaceIdx(1),
                                                                ),
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
                                    idx: 11,
                                    src: ExpectationSource {
                                        syn_expr_idx: 12,
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
                                        syn_expr_idx: 13,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
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
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                Transient,
                                            ),
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    1,
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 13,
                                    src: ExpectationSource {
                                        syn_expr_idx: 14,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(3),
                                                ),
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
                                                            expectee_quary: ImmutableOnStack {
                                                                place: Idx(
                                                                    PlaceIdx(3),
                                                                ),
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`unit`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 14,
                                    src: ExpectationSource {
                                        syn_expr_idx: 15,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
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
                                    idx: 15,
                                    src: ExpectationSource {
                                        syn_expr_idx: 16,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                Transient,
                                            ),
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    0,
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 16,
                                    src: ExpectationSource {
                                        syn_expr_idx: 17,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(2),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: ImmutableOnStack {
                                                                place: Idx(
                                                                    PlaceIdx(2),
                                                                ),
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`unit`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 17,
                                    src: ExpectationSource {
                                        syn_expr_idx: 18,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
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
                                    idx: 18,
                                    src: ExpectationSource {
                                        syn_expr_idx: 19,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                        syn_expr_idx: 20,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Leash ConnectedComponent`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 20,
                                    src: ExpectationSource {
                                        syn_expr_idx: 21,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`ConnectedComponent`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Redirection(
                                                        Releash,
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
                                                EthTerm(`Leash ConnectedComponent`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 21,
                                    src: ExpectationSource {
                                        syn_expr_idx: 22,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`never`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Never,
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
                EthTerm(`Leash ConnectedComponent`),
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
            ItemPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::ignored_connected_components_row_span_sum_sum`),
            ),
            place_registry: PlaceRegistry {
                infos: [
                    PlaceInfo::Variable {
                        current_variable_idx: 0,
                        ident: `sum`,
                    },
                    PlaceInfo::Variable {
                        current_variable_idx: 1,
                        ident: `i`,
                    },
                ],
            },
            sem_expr_arena: SemExprArena(
                Arena {
                    data: [
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        5,
                                    ),
                                    LiteralTokenData::Float(
                                        Unspecified(
                                            UnspecifiedFloatLiteral(
                                                Id {
                                                    value: 2,
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
                                    base: FlyTermBase::Hol(
                                        HolTerm(
                                            0,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    0,
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
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 0,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::connected_components`),
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
                                        EthTerm(`Leash Vec ConnectedComponent`),
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                            EthTerm(`Vec ConnectedComponent`),
                                        ),
                                    },
                                    self_contract: Contract::Pure,
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        10,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `ilen`,
                                        regional_token_idx: RegionalTokenIdx(
                                            11,
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
                                                    `core::vec::Vec(0)::ilen`,
                                                    TypeItemKind::MethodRitchie(
                                                        RitchieItemKind::Fn,
                                                    ),
                                                ),
                                                self_value_parameter: FlyRitchieSimpleParameter {
                                                    contract: Contract::Pure,
                                                    ty: FlyTerm {
                                                        quary: None,
                                                        base: FlyTermBase::Eth(
                                                            EthTerm(`Vec ConnectedComponent`),
                                                        ),
                                                    },
                                                },
                                                parenate_parameters: [],
                                                self_ty: FlyTerm {
                                                    quary: None,
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`Vec ConnectedComponent`),
                                                    ),
                                                },
                                                return_ty: FlyTerm {
                                                    quary: Some(
                                                        Transient,
                                                    ),
                                                    base: FlyTermBase::Eth(
                                                        EthTerm(`i32`),
                                                    ),
                                                },
                                                instantiation: FlyInstantiation {
                                                    path: ItemPath(`core::vec::Vec(0)::ilen`),
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
                                                                        EthTerm(`ConnectedComponent`),
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
                                        12,
                                    ),
                                    ritchie_parameter_argument_matches: [],
                                    rpar_regional_token_idx: RegionalTokenIdx(
                                        13,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        Transient,
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
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
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::FrameVarDecl {
                                    regional_token_idx: RegionalTokenIdx(
                                        7,
                                    ),
                                    ident: `i`,
                                    for_loop_varible_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        2,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(1),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    3,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        15,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(0),
                                            ),
                                        },
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
                                    4,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                SemExprData::PrincipalEntityPath {
                                    path_expr_idx: 1,
                                    path: PrincipalEntityPath::MajorItem(
                                        MajorItemPath::Form(
                                            MajorFormPath(`mnist_classifier::major::connected_components`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::connected_components`),
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
                                        EthTerm(`Leash Vec ConnectedComponent`),
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `i`,
                                    regional_token_idx: RegionalTokenIdx(
                                        19,
                                    ),
                                    current_variable_idx: 1,
                                    current_variable_kind: CurrentVariableKind::LoopVariable(
                                        2,
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        ImmutableOnStack {
                                            place: Idx(
                                                PlaceIdx(1),
                                            ),
                                        },
                                    ),
                                    base: FlyTermBase::Eth(
                                        EthTerm(`i32`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    6,
                                    FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Index {
                                    self_argument: SemExprIdx(
                                        5,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        18,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                6,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        20,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`ConnectedComponent`),
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
                                        EthTerm(`ConnectedComponent`),
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
                                            EthTerm(`ConnectedComponent`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Field {
                                    self_argument: SemExprIdx(
                                        7,
                                    ),
                                    self_argument_ty: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`ConnectedComponent`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        21,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `row_span_sum`,
                                        regional_token_idx: RegionalTokenIdx(
                                            22,
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
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`),
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
                                    8,
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
                                        4,
                                    ),
                                    opr: AssignClosed(
                                        Add,
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
                                        16,
                                    ),
                                    ropd: SemExprIdx(
                                        8,
                                    ),
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
                            expectation_idx_and_ty: Some(
                                (
                                    9,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::CurrentVariable {
                                    ident: `sum`,
                                    regional_token_idx: RegionalTokenIdx(
                                        24,
                                    ),
                                    current_variable_idx: 0,
                                    current_variable_kind: CurrentVariableKind::LetVariable {
                                        pattern_variable_idx: 0,
                                    },
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: Some(
                                        MutableOnStack {
                                            place: Idx(
                                                PlaceIdx(0),
                                            ),
                                        },
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
                                    10,
                                    FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                    11,
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
                                        27,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `row_span_sum`,
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
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::row_span_sum`),
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
                                    12,
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
                                        10,
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
                                        25,
                                    ),
                                    ropd: SemExprIdx(
                                        12,
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
                                    13,
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
                                            1..4,
                                        ),
                                    ),
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`never`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    14,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`never`),
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
                                        9,
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
                                    contract: Contract::Move,
                                    eq_token: EqRegionalToken(
                                        RegionalTokenIdx(
                                            4,
                                        ),
                                    ),
                                    initial_value: SemExprIdx(
                                        0,
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
                                SemStmtData::ForBetween {
                                    for_token: StmtForRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            6,
                                        ),
                                    },
                                    particulars: SemForBetweenParticulars {
                                        for_between_loop_var_regional_token_idx: RegionalTokenIdx(
                                            7,
                                        ),
                                        for_between_loop_var_ident: `i`,
                                        for_between_loop_var_expr_idx: SemExprIdx(
                                            3,
                                        ),
                                        range: SemaForBetweenRange {
                                            initial_boundary: SemaForBetweenLoopBoundary {
                                                bound_expr: None,
                                                kind: LowerClosed,
                                            },
                                            final_boundary: SemaForBetweenLoopBoundary {
                                                bound_expr: Some(
                                                    SemExprIdx(
                                                        2,
                                                    ),
                                                ),
                                                kind: UpperOpen,
                                            },
                                            step: Constant(
                                                1,
                                            ),
                                        },
                                    },
                                    for_loop_varible_idx: 1,
                                    eol_colon: EolRegionalToken::Colon(
                                        EolColonRegionalToken {
                                            regional_token_idx: RegionalTokenIdx(
                                                14,
                                            ),
                                        },
                                    ),
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
                                        EthTerm(`unit`),
                                    ),
                                },
                            ),
                        },
                        SemStmtEntry {
                            data_result: Ok(
                                SemStmtData::Return {
                                    return_token: ReturnRegionalToken {
                                        regional_token_idx: RegionalTokenIdx(
                                            23,
                                        ),
                                    },
                                    result: SemExprIdx(
                                        13,
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
                                },
                            ),
                            ty_result: Ok(
                                FlyTerm {
                                    quary: None,
                                    base: FlyTermBase::Eth(
                                        EthTerm(`never`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    15,
                    (
                        SemExprIdx(
                            14,
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
                                Compterm,
                            ),
                            base: Hol(
                                HolTerm(
                                    0,
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
                                        Compterm,
                                    ),
                                    base: Hol(
                                        HolTerm(
                                            0,
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
                        0,
                    ),
                    Ok(
                        FlyTerm {
                            quary: None,
                            base: FlyTermBase::Eth(
                                EthTerm(`0.0f32`),
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
                                MutableOnStack {
                                    place: Idx(
                                        PlaceIdx(0),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Hol(
                                HolTerm(
                                    0,
                                ),
                            ),
                        },
                    ),
                    SymbolType(
                        FlyTerm {
                            quary: Some(
                                ImmutableOnStack {
                                    place: Idx(
                                        PlaceIdx(1),
                                    ),
                                },
                            ),
                            base: FlyTermBase::Eth(
                                EthTerm(`i32`),
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
                                        0,
                                    ),
                                    hole_kind: UnspecifiedFloatType,
                                    fill: Some(
                                        FlyTerm {
                                            quary: Some(
                                                Transient,
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    ),
                                    constraints: [
                                        HoleConstraint::CoercibleFrom {
                                            target: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`f32`),
                                                ),
                                            },
                                        },
                                    ],
                                },
                                resolve_progress: HolTermResolveProgressBuf::ResolvedEthereal(
                                    EthTerm(`f32`),
                                ),
                            },
                        ],
                        first_unresolved_term_idx: 1,
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
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
                                                ImmutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(1),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Eth(
                                                EthTerm(`i32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 2,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Trivial(
                                                        TrivialFlyCoercion {
                                                            expectee_quary: ImmutableOnStack {
                                                                place: Idx(
                                                                    PlaceIdx(1),
                                                                ),
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
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 8,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                            EthTerm(`Leash Vec ConnectedComponent`),
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
                                            ImmutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(1),
                                                ),
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`i32`),
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
                                            EthTerm(`ConnectedComponent`),
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
                                            quary: Some(
                                                MutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    0,
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 8,
                                    src: ExpectationSource {
                                        syn_expr_idx: 9,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`unit`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 9,
                                    src: ExpectationSource {
                                        syn_expr_idx: 10,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`unit`),
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
                                    idx: 10,
                                    src: ExpectationSource {
                                        syn_expr_idx: 12,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            MutableOnStack {
                                                place: Idx(
                                                    PlaceIdx(0),
                                                ),
                                            },
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
                                expectation: Expectation::AnyOriginal(
                                    ExpectAnyOriginal,
                                ),
                                state: ExpectationState {
                                    idx: 11,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Pure,
                                        ty_expected: FlyTerm {
                                            quary: Some(
                                                MutableOnStack {
                                                    place: Idx(
                                                        PlaceIdx(0),
                                                    ),
                                                },
                                            ),
                                            base: FlyTermBase::Hol(
                                                HolTerm(
                                                    0,
                                                ),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 12,
                                    src: ExpectationSource {
                                        syn_expr_idx: 13,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 13,
                                    src: ExpectationSource {
                                        syn_expr_idx: 14,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`f32`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 14,
                                    src: ExpectationSource {
                                        syn_expr_idx: 15,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`never`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Never,
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
                EthTerm(`f32`),
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
            ItemPath(`mnist_classifier::major::major_raw_contours`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::major_raw_contours`),
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
                                        2,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `raw_contours`,
                                        regional_token_idx: RegionalTokenIdx(
                                            3,
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
                                                    EthTerm(`Vec RawContour`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Vec RawContour`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash Vec RawContour`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`),
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
                                        EthTerm(`Leash Vec RawContour`),
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
                                            EthTerm(`Leash Vec RawContour`),
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
                                        EthTerm(`Leash Vec RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec RawContour`),
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
                                        1,
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
                                        EthTerm(`Leash Vec RawContour`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    2,
                    (
                        SemExprIdx(
                            2,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Leash Vec RawContour`),
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
                                            EthTerm(`Leash Vec RawContour`),
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
                                                EthTerm(`Leash Vec RawContour`),
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
                                            EthTerm(`Leash Vec RawContour`),
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
                EthTerm(`Leash Vec RawContour`),
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
            ItemPath(`mnist_classifier::major::major_raw_contour`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::major_raw_contour`),
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
                                        2,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `raw_contours`,
                                        regional_token_idx: RegionalTokenIdx(
                                            3,
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
                                                    EthTerm(`Vec RawContour`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Vec RawContour`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash Vec RawContour`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::connected_component::ConnectedComponent(0)::raw_contours`),
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
                                        EthTerm(`Leash Vec RawContour`),
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
                                            EthTerm(`Leash Vec RawContour`),
                                        ),
                                    },
                                ),
                            ),
                        },
                        SemExprEntry {
                            data_result: Ok(
                                SemExprData::Literal(
                                    RegionalTokenIdx(
                                        5,
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
                                            0,
                                        ),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
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
                                        1,
                                    ),
                                    lbox_regional_token_idx: RegionalTokenIdx(
                                        4,
                                    ),
                                    items: [
                                        SemCommaListItem {
                                            expr: SemExprIdx(
                                                2,
                                            ),
                                            comma_regional_token_idx: None,
                                        },
                                    ],
                                    rbox_regional_token_idx: RegionalTokenIdx(
                                        6,
                                    ),
                                    index_dynamic_dispatch: FlyInstanceDispatch {
                                        indirections: FlyIndirections {
                                            initial_place: Transient,
                                            indirections: [
                                                Leash,
                                            ],
                                            final_place: Leashed {
                                                place: None,
                                            },
                                        },
                                        signature: FlyIndexSignature::Int {
                                            element_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`RawContour`),
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
                                        EthTerm(`RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    4,
                                    FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`RawContour`),
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
                                        EthTerm(`Leash RawContour`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    5,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RawContour`),
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
                                        3,
                                    ),
                                    outcome: Some(
                                        ExpectationOutcome::Coercion(
                                            ExpectCoercionOutcome {
                                                coercion: Redirection(
                                                    Releash,
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
                                        EthTerm(`Leash RawContour`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    4,
                    (
                        SemExprIdx(
                            4,
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
                        2,
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
                        entries: [
                            HolTermEntry {
                                data: HolTermData::Hole {
                                    hole_source: HoleSource::Expr(
                                        2,
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
                        ],
                        first_unresolved_term_idx: 1,
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
                                        syn_expr_idx: 1,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Transient,
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec RawContour`),
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
                                    idx: 3,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
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
                                expectation: Expectation::Coercion(
                                    ExpectCoercion {
                                        contract: Contract::Move,
                                        ty_expected: FlyTerm {
                                            quary: None,
                                            base: FlyTermBase::Eth(
                                                EthTerm(`Leash RawContour`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 4,
                                    src: ExpectationSource {
                                        syn_expr_idx: 3,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: Some(
                                            Leashed {
                                                place: None,
                                            },
                                        ),
                                        base: FlyTermBase::Eth(
                                            EthTerm(`RawContour`),
                                        ),
                                    },
                                    resolve_progress: ExpectationProgress::Resolved(
                                        Ok(
                                            ExpectationOutcome::Coercion(
                                                ExpectCoercionOutcome {
                                                    coercion: Redirection(
                                                        Releash,
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
                                                EthTerm(`Leash RawContour`),
                                            ),
                                        },
                                    },
                                ),
                                state: ExpectationState {
                                    idx: 5,
                                    src: ExpectationSource {
                                        syn_expr_idx: 4,
                                        kind: Expr,
                                    },
                                    expectee: FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash RawContour`),
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
                EthTerm(`Leash RawContour`),
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
            ItemPath(`mnist_classifier::major::major_line_segment_sketch`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::major_line_segment_sketch`),
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
                                            MajorFormPath(`mnist_classifier::major::major_raw_contour`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_raw_contour`),
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
                                        EthTerm(`Leash RawContour`),
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
                                            EthTerm(`Leash RawContour`),
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
                                            EthTerm(`Leash RawContour`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `line_segment_sketch`,
                                        regional_token_idx: RegionalTokenIdx(
                                            3,
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
                                                    EthTerm(`LineSegmentSketch`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`LineSegmentSketch`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash LineSegmentSketch`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::raw_contour::RawContour(0)::line_segment_sketch`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::raw_contour::RawContour(0)::line_segment_sketch`),
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
                                        EthTerm(`Leash LineSegmentSketch`),
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
                                            EthTerm(`Leash LineSegmentSketch`),
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
                                        EthTerm(`Leash LineSegmentSketch`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash LineSegmentSketch`),
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
                                        1,
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
                                        EthTerm(`Leash LineSegmentSketch`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    2,
                    (
                        SemExprIdx(
                            2,
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
                                            EthTerm(`Leash RawContour`),
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
                                                EthTerm(`Leash LineSegmentSketch`),
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
                                            EthTerm(`Leash LineSegmentSketch`),
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
                                                EthTerm(`Leash LineSegmentSketch`),
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
                                            EthTerm(`Leash LineSegmentSketch`),
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
                EthTerm(`Leash LineSegmentSketch`),
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
            ItemPath(`mnist_classifier::major::major_concave_components`),
        ),
        data: SemExprRegionData {
            path: RegionPath::ItemDefn(
                ItemPath(`mnist_classifier::major::major_concave_components`),
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
                                            MajorFormPath(`mnist_classifier::major::major_line_segment_sketch`, `Val`),
                                        ),
                                    ),
                                    ty_path_disambiguation: InstanceConstructor,
                                    instantiation: Some(
                                        FlyInstantiation {
                                            path: ItemPath(`mnist_classifier::major::major_line_segment_sketch`),
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
                                        EthTerm(`Leash LineSegmentSketch`),
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
                                            EthTerm(`Leash LineSegmentSketch`),
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
                                            EthTerm(`Leash LineSegmentSketch`),
                                        ),
                                    },
                                    dot_regional_token_idx: RegionalTokenIdx(
                                        2,
                                    ),
                                    ident_token: IdentRegionalToken {
                                        ident: `concave_components`,
                                        regional_token_idx: RegionalTokenIdx(
                                            3,
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
                                                    EthTerm(`Vec ConcaveComponent`),
                                                ),
                                            },
                                            return_ty: FlyTerm {
                                                quary: Some(
                                                    Transient,
                                                ),
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Vec ConcaveComponent`),
                                                ),
                                            },
                                            expr_ty: FlyTerm {
                                                quary: None,
                                                base: FlyTermBase::Eth(
                                                    EthTerm(`Leash Vec ConcaveComponent`),
                                                ),
                                            },
                                            path: AssocItemPath::TypeItem(
                                                TypeItemPath(
                                                    `mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::concave_components`,
                                                    TypeItemKind::MemoizedField,
                                                ),
                                            ),
                                            instantiation: FlyInstantiation {
                                                path: ItemPath(`mnist_classifier::line_segment_sketch::LineSegmentSketch(0)::concave_components`),
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
                                        EthTerm(`Leash Vec ConcaveComponent`),
                                    ),
                                },
                            ),
                            expectation_idx_and_ty: Some(
                                (
                                    2,
                                    FlyTerm {
                                        quary: None,
                                        base: FlyTermBase::Eth(
                                            EthTerm(`Leash Vec ConcaveComponent`),
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
                                        1,
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
                                        EthTerm(`Leash Vec ConcaveComponent`),
                                    ),
                                },
                            ),
                        },
                    ],
                },
            ),
            sem_expr_roots: [
                (
                    2,
                    (
                        SemExprIdx(
                            2,
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
                                            EthTerm(`Leash LineSegmentSketch`),
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
                                                EthTerm(`Leash Vec ConcaveComponent`),
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
                        ],
                    },
                    first_unresolved_expectation: 0,
                },
            },
            return_ty: Some(
                EthTerm(`Leash Vec ConcaveComponent`),
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