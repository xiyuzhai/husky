pub(crate) use expect_test::*;
pub(crate) use husky_vfs::test_helpers::*;

use expect_test::{expect, Expect};
use husky_vfs::jar::VfsDb;
use husky_vfs::script::Script;
use salsa::DebugWithDb;

#[salsa::db(
    husky_coword::jar::CowordJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    husky_term_prelude::jar::TermPreludeJar,
    husky_token_data::jar::TokenDataJar,
    husky_text::jar::TextJar,
    husky_token::jar::TokenJar,
    husky_ast::jar::AstJar,
    husky_entity_tree::jar::EntityTreeJar,
    husky_toml_token::jar::TomlTokenJar,
    husky_toml_ast::jar::TomlAstJar,
    husky_manifest_ast::jar::ManifestAstJar,
    husky_corgi_config::jar::CorgiConfigJar,
    husky_corgi_config_ast::jar::CorgiConfigAstJar,
    husky_manifest::jar::ManifestJar,
    crate::Jar
)]
pub(crate) struct DB;

pub(crate) fn t<'a>(db: &DB, input: &str, expected: &Expect) {
    let toolchain = db.dev_toolchain().unwrap();
    let path_menu = db.vfs_path_menu(toolchain);
    let snippet = Script::new_dev_snippet(input, db);
    let (expr_region, expr_idx) =
        crate::snippet::parse_expr_from_script(db, path_menu.core_library(), snippet)
            .as_ref()
            .unwrap();
    expected.assert_debug_eq(&(expr_region.data(db).debug_with(db), *expr_idx));
}

#[test]
fn parse_expr_works() {
    let db = &DB::default();

    t(
        db,
        "1",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "1",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    1,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        1,
                                    ),
                                ),
                            ),
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 0,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    0,
                ),
            )
        "#]],
    );

    t(
        db,
        "-1",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "-1",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    2,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        1,
                                    ),
                                ),
                            ),
                            SynExprData::Prefix {
                                opr: Minus,
                                opr_regional_token_idx: RegionalTokenIdx(
                                    1,
                                ),
                                opd: 0,
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 1,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    1,
                ),
            )
        "#]],
    );

    t(
        db,
        "1i32",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "1i32",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    1,
                                ),
                                LiteralTokenData::Integer(
                                    I32(
                                        1,
                                    ),
                                ),
                            ),
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 0,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    0,
                ),
            )
        "#]],
    );

    t(
        db,
        "2i64",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "2i64",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    1,
                                ),
                                LiteralTokenData::Integer(
                                    I64(
                                        2,
                                    ),
                                ),
                            ),
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 0,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    0,
                ),
            )
        "#]],
    );

    t(
        db,
        "22222222222222222222222222222222222222222222i64",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "22222222222222222222222222222222222222222222i64",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Err(
                                SynExprError::Derived(
                                    DerivedSynExprError::TokenData(
                                        TokenDataError::ParseIntError,
                                    ),
                                ),
                            ),
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 0,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    0,
                ),
            )
        "#]],
    );

    t(
        db,
        "1 + 1",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "1 + 1",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    1,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        1,
                                    ),
                                ),
                            ),
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    3,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        1,
                                    ),
                                ),
                            ),
                            SynExprData::Binary {
                                lopd: 0,
                                opr: SynBinaryOpr::Closed(
                                    BinaryClosedOpr::Add,
                                ),
                                opr_regional_token_idx: RegionalTokenIdx(
                                    2,
                                ),
                                ropd: 1,
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 2,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    2,
                ),
            )
        "#]],
    );

    t(
        db,
        "[]i32",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "[]i32",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::List {
                                lbox_regional_token_idx: RegionalTokenIdx(
                                    1,
                                ),
                                items: [],
                                rbox_regional_token_idx: RegionalTokenIdx(
                                    2,
                                ),
                            },
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            3,
                                        ),
                                        ident: `i32`,
                                    },
                                ),
                            ),
                            SynExprData::ExplicitApplication {
                                function_expr_idx: 0,
                                argument_expr_idx: 1,
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 2,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    2,
                ),
            )
        "#]],
    );

    t(
        db,
        "[3]i32",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "[3]i32",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    2,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        3,
                                    ),
                                ),
                            ),
                            SynExprData::List {
                                lbox_regional_token_idx: RegionalTokenIdx(
                                    1,
                                ),
                                items: [
                                    SynCommaListItem {
                                        syn_expr_idx: 0,
                                        comma_regional_token_idx: None,
                                    },
                                ],
                                rbox_regional_token_idx: RegionalTokenIdx(
                                    3,
                                ),
                            },
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            4,
                                        ),
                                        ident: `i32`,
                                    },
                                ),
                            ),
                            SynExprData::ExplicitApplication {
                                function_expr_idx: 1,
                                argument_expr_idx: 2,
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 3,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    3,
                ),
            )
        "#]],
    );

    t(
        db,
        "(i32, i32)",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "(i32, i32)",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            2,
                                        ),
                                        ident: `i32`,
                                    },
                                ),
                            ),
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            4,
                                        ),
                                        ident: `i32`,
                                    },
                                ),
                            ),
                            SynExprData::NewTuple {
                                lpar_regional_token_idx: RegionalTokenIdx(
                                    1,
                                ),
                                items: [
                                    SynCommaListItem {
                                        syn_expr_idx: 0,
                                        comma_regional_token_idx: Some(
                                            RegionalTokenIdx(
                                                3,
                                            ),
                                        ),
                                    },
                                    SynCommaListItem {
                                        syn_expr_idx: 1,
                                        comma_regional_token_idx: None,
                                    },
                                ],
                                rpar_regional_token_idx: RegionalTokenIdx(
                                    5,
                                ),
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 2,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    2,
                ),
            )
        "#]],
    );

    t(
        db,
        "x.a",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "x.a",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                        ident: `x`,
                                    },
                                ),
                            ),
                            SynExprData::Field {
                                owner: 0,
                                dot_regional_token_idx: RegionalTokenIdx(
                                    2,
                                ),
                                ident_token: IdentRegionalToken {
                                    ident: `a`,
                                    regional_token_idx: RegionalTokenIdx(
                                        3,
                                    ),
                                },
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 1,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    1,
                ),
            )
        "#]],
    );

    t(
        db,
        "x.len()",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "x.len()",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Err(
                                SynExprError::Original(
                                    OriginalSynExprError::UnrecognizedIdent {
                                        regional_token_idx: RegionalTokenIdx(
                                            1,
                                        ),
                                        ident: `x`,
                                    },
                                ),
                            ),
                            SynExprData::MethodApplicationOrCall {
                                self_argument: 0,
                                dot_regional_token_idx: RegionalTokenIdx(
                                    2,
                                ),
                                ident_token: IdentRegionalToken {
                                    ident: `len`,
                                    regional_token_idx: RegionalTokenIdx(
                                        3,
                                    ),
                                },
                                template_arguments: None,
                                lpar_regional_token_idx: RegionalTokenIdx(
                                    4,
                                ),
                                items: [],
                                rpar_regional_token_idx: RegionalTokenIdx(
                                    5,
                                ),
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 1,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    1,
                ),
            )
        "#]],
    );
}

#[test]
fn parse_application_expr_works() {
    let db = &DB::default();
    // this doesn't make sense semantically, but useful for specifying syntactic behavior
    t(
        db,
        "0 1 2",
        &expect![[r#"
            (
                SynExprRegionData {
                    parent: None,
                    path: SynNodeRegionPath::ItemDefn(
                        ItemSynNodePath::Script(
                            Room32,
                            ScriptSynNodePath(
                                ItemSynNodePathId {
                                    data: ItemSynNodePathData::Script(
                                        ScriptSynNodePathData {
                                            script: Script {
                                                source: Snippet {
                                                    toolchain: Toolchain(
                                                        Id {
                                                            value: 1,
                                                        },
                                                    ),
                                                },
                                                data: "0 1 2",
                                            },
                                        },
                                    ),
                                },
                            ),
                        ),
                    ),
                    expr_arena: Arena {
                        data: [
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    1,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        0,
                                    ),
                                ),
                            ),
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    2,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        1,
                                    ),
                                ),
                            ),
                            SynExprData::ExplicitApplication {
                                function_expr_idx: 0,
                                argument_expr_idx: 1,
                            },
                            SynExprData::Literal(
                                RegionalTokenIdx(
                                    3,
                                ),
                                LiteralTokenData::Integer(
                                    UnspecifiedRegular(
                                        2,
                                    ),
                                ),
                            ),
                            SynExprData::ExplicitApplication {
                                function_expr_idx: 2,
                                argument_expr_idx: 3,
                            },
                        ],
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
                        allow_self_type: False,
                        allow_self_value: False,
                        pattern_ty_constraints: [],
                    },
                    pattern_roots: [],
                    expr_roots: [
                        SynExprRoot {
                            kind: SynExprRootKind::Snippet,
                            syn_expr_idx: 4,
                        },
                    ],
                    has_self_lifetime: false,
                    has_self_place: false,
                    pattern_to_current_variable_map: [],
                },
                Some(
                    4,
                ),
            )
        "#]],
    );
}
