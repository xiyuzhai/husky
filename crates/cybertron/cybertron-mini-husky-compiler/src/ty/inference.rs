use super::*;
use crate::resolution::SymbolResolution;
use resolution::calc_symbol_resolutions;
use scope::infer_scopes;
use signature::{calc_ty_signatures, TypeSignature, TypeSignatureKey};
use term::calc_ty_terms;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TypeInference {
    pub ty: Type,
}

pub fn calc_ty_inferences(
    asts: Seq<Option<Ast>>,
    symbol_resolutions: Seq<Option<SymbolResolution>>,
    roles: Seq<Option<Role>>,
    ty_terms: Seq<Option<Type>>,
    ty_signatures: Seq<Option<TypeSignature>>,
    n: usize,
) -> Seq<Option<TypeInference>> {
    let mut ty_inferences = infer_tys_initial(asts, ty_signatures);
    let mut ty_designations =
        calc_initial_ty_designations(asts, roles, symbol_resolutions, ty_inferences, ty_terms);
    for _ in 0..n {
        ty_inferences |= infer_tys_step(asts, symbol_resolutions, ty_inferences, ty_designations);
        ty_designations |= calc_ty_designations_step(roles, symbol_resolutions, ty_inferences);
    }
    ty_inferences
}

fn infer_tys_initial(
    asts: Seq<Option<Ast>>,
    ty_signatures: Seq<Option<TypeSignature>>,
) -> Seq<Option<TypeInference>> {
    inference_literal_tys(asts).or(infer_fn_call_tys(asts, ty_signatures))
}
fn inference_literal_tys(asts: Seq<Option<Ast>>) -> Seq<Option<TypeInference>> {
    asts.map(|ast| match ast?.data {
        AstData::Literal(lit) => match lit {
            Literal::Int(_) => Some(TypeInference {
                ty: Type::new_ident(Ident::new("Int")),
            }),
            Literal::Float(_) => Some(TypeInference {
                ty: Type::new_ident(Ident::new("Float")),
            }),
        },
        _ => None,
    })
}

fn infer_fn_call_tys(
    asts: Seq<Option<Ast>>,
    ty_signatures: Seq<Option<TypeSignature>>,
) -> Seq<Option<TypeInference>> {
    ty_signatures
        .first_filtered_by_attention(asts, ty_signatures, |ast, ty_signature| {
            let Some(ast) = ast else { return false };
            let Some(TypeSignature {
                key: TypeSignatureKey::FnOutput { fn_ident },
                ..
            }) = ty_signature
            else {
                return false;
            };
            match ast.data {
                AstData::Call {
                    caller,
                    caller_ident,
                    left_delimiter,
                    right_delimiter,
                    delimited_arguments,
                } if caller_ident == Some(fn_ident) => true,
                _ => false,
            }
        })
        .map(|ty_inference| {
            Some(TypeInference {
                ty: ty_inference??.ty,
            })
        })
}

#[test]
fn infer_tys_initial_works() {
    fn t(input: &str, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
        let scopes = infer_scopes(asts, 10);
        let roles = calc_roles(asts, scopes, 10);
        let ranks = calc_ranks(asts);
        let ty_terms = calc_ty_terms(asts, roles, 10);
        let ty_signatures = calc_ty_signatures(asts, roles, ty_terms);
        let ty_inferences_initial = infer_tys_initial(asts, ty_signatures);
        expect.assert_debug_eq(&show_asts_mapped_values(
            tokens,
            asts,
            ty_inferences_initial,
        ));
    }
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "struct A {}",
        expect![[r#"
        [
            #0 `struct`: "struct A {}" ✓,
            #1 `A`: "A",
            #2 `{`: `{`,
            #3 `}`: "{}",
        ]
    "#]],
    );
    t(
        "fn f(x: i32) { let y = x; let t: i32 = x + 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : i32) { let y = x; let t : i32 = x + 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : i32",
                #5 `i32`: "i32",
                #6 `)`: "(x : i32)",
                #7 `{`: "(x : i32) { let y = x; let t : i32 = x + 1;  }",
                #8 `let`: "let y = x",
                #9 `y`: "y",
                #10 `=`: "y = x",
                #11 `x`: "x",
                #12 `;`: "let y = x; ",
                #13 `let`: "let t : i32 = x + 1",
                #14 `t`: "t",
                #15 `:`: "t : i32",
                #16 `i32`: "i32",
                #17 `=`: "t : i32 = x + 1",
                #18 `x`: "x",
                #19 `+`: "x + 1",
                #20 `1`: "1" → TypeInference { ty: `Int` },
                #21 `;`: "let t : i32 = x + 1; ",
                #22 `}`: "{ let y = x; let t : i32 = x + 1;  }",
            ]
        "#]],
    );
    t(
        "fn f() -> i32 { return 1; } fn g() { let x = f(); g() }",
        expect![[r#"
            [
                #0 `fn`: "fn f() -> i32 { return 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `->`: "() -> i32",
                #5 `i32`: "i32",
                #6 `{`: "() -> i32 { return 1;  }",
                #7 `return`: "return 1",
                #8 `1`: "1" → TypeInference { ty: `Int` },
                #9 `;`: "return 1; ",
                #10 `}`: "{ return 1;  }",
                #11 `fn`: "fn g() { let x = f(); g() }" ✓,
                #12 `g`: "g",
                #13 `(`: `(`,
                #14 `)`: "()",
                #15 `{`: "() { let x = f(); g() }",
                #16 `let`: "let x = f()",
                #17 `x`: "x",
                #18 `=`: "x = f()",
                #19 `f`: "f",
                #20 `(`: "f()" → TypeInference { ty: `i32` },
                #21 `)`: "()",
                #22 `;`: "let x = f(); ",
                #23 `g`: "g",
                #24 `(`: "g()" → TypeInference { ty: `unit` },
                #25 `)`: "()",
                #26 `}`: "{ let x = f(); g() }",
            ]
        "#]],
    );
}

fn infer_tys_step(
    asts: Seq<Option<Ast>>,
    symbol_resolutions: Seq<Option<SymbolResolution>>,
    ty_inferences: Seq<Option<TypeInference>>,
    ty_designations: Seq<Option<TypeDesignation>>,
) -> Seq<Option<TypeInference>> {
    let mut ty_inferences = ty_designations
        .first_filtered_by_attention(
            symbol_resolutions,
            ty_designations,
            |symbol_resolution, ty_designation| {
                let Some(SymbolResolution::Ok(symbol)) = symbol_resolution else {
                    return false;
                };
                let Some(ty_designation) = ty_designation else {
                    return false;
                };
                symbol == ty_designation.symbol
            },
        )
        .map(Option::flatten)
        .map(|ty_designation| {
            Some(TypeInference {
                ty: ty_designation?.ty,
            })
        });
    ty_inferences |= {
        let fsts = ty_inferences
            .index(
                (|ast: Option<Ast>| match ast?.data {
                    AstData::Prefix { opr, opd } => Some(opd),
                    AstData::Binary {
                        lopd,
                        lopd_ident,
                        opr,
                        ropd,
                    } => Some(lopd),
                    AstData::Suffix { opd, opr } => Some(opd),
                    _ => None,
                })
                .apply(asts),
            )
            .map(Option::flatten);
        let snds = ty_inferences
            .index(
                (|ast: Option<Ast>| match ast?.data {
                    AstData::Binary { ropd, .. } => Some(ropd),
                    _ => None,
                })
                .apply(asts),
            )
            .map(Option::flatten);
        (|ast: Option<Ast>, fst: Option<TypeInference>, snd: Option<TypeInference>| match ast?.data
        {
            AstData::Prefix { opr, opd } => match opr {
                PrefixOpr::Not => match fst?.ty {
                    ty @ Type::Rec0(ident) => match ident.0.repr() {
                        "Bool" => Some(TypeInference { ty }),
                        _ => None,
                    },
                    _ => None,
                },
                PrefixOpr::Minus | PrefixOpr::Plus => match fst?.ty {
                    ty @ Type::Rec0(ident) => match ident.0.repr() {
                        "Int" | "Float" => Some(TypeInference { ty }),
                        _ => None,
                    },
                    _ => None,
                },
            },
            AstData::Binary {
                lopd,
                lopd_ident,
                opr,
                ropd,
            } => match opr {
                BinaryOpr::Add | BinaryOpr::Sub | BinaryOpr::Mul | BinaryOpr::Div => {
                    let fst = fst?;
                    let snd = snd?;
                    if fst != snd {
                        return None;
                    }
                    match fst.ty {
                        Type::Rec0(_) => todo!(),
                        Type::Rec1(_) => todo!(),
                        Type::Rec2(_) => todo!(),
                        Type::Rec3(_) => todo!(),
                        Type::Rec4(_) => todo!(),
                        Type::Rec5(_) => todo!(),
                        Type::Rec6(_) => todo!(),
                        Type::Rec7(_) => todo!(),
                        Type::Rec8(_) => todo!(),
                        Type::Rec9(_) => todo!(),
                        Type::Rec10(_) => todo!(),
                    }
                }
                BinaryOpr::Assign => None,
                BinaryOpr::Eq | BinaryOpr::Ne => Some(TypeInference {
                    ty: Type::new_ident(Ident::new("Bool")),
                }),
                BinaryOpr::ScopeResolution => None,
                BinaryOpr::TypeIs => None,
                BinaryOpr::LightArrow => None,
                BinaryOpr::Vertical => todo!(),
            },
            AstData::Suffix { opd, opr } => match opr {
                SuffixOpr::Incr | SuffixOpr::Decr => todo!(),
                SuffixOpr::Field(_) => None,
            },
            _ => None,
        })
        .apply(asts, fsts, snds)
    };
    ty_inferences
}

#[test]
fn calc_ty_inferences_works() {
    fn t(input: &str, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
        let scopes = infer_scopes(asts, 10);
        let roles = calc_roles(asts, scopes, 10);
        let ranks = calc_ranks(asts);
        let ty_terms = calc_ty_terms(asts, roles, 10);
        let ty_signatures = calc_ty_signatures(asts, roles, ty_terms);
        let symbol_resolutions = calc_symbol_resolutions(asts, 10);
        let ty_inferences =
            calc_ty_inferences(asts, symbol_resolutions, roles, ty_terms, ty_signatures, 10);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ty_inferences));
    }
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "struct A {}",
        expect![[r#"
        [
            #0 `struct`: "struct A {}" ✓,
            #1 `A`: "A",
            #2 `{`: `{`,
            #3 `}`: "{}",
        ]
    "#]],
    );
    t(
        "fn f(x: i32) { let y = x; let t: i32 = x + 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : i32) { let y = x; let t : i32 = x + 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : i32",
                #5 `i32`: "i32",
                #6 `)`: "(x : i32)",
                #7 `{`: "(x : i32) { let y = x; let t : i32 = x + 1;  }",
                #8 `let`: "let y = x",
                #9 `y`: "y",
                #10 `=`: "y = x",
                #11 `x`: "x",
                #12 `;`: "let y = x; ",
                #13 `let`: "let t : i32 = x + 1",
                #14 `t`: "t" → TypeInference { ty: `i32` },
                #15 `:`: "t : i32",
                #16 `i32`: "i32",
                #17 `=`: "t : i32 = x + 1",
                #18 `x`: "x",
                #19 `+`: "x + 1",
                #20 `1`: "1" → TypeInference { ty: `Int` },
                #21 `;`: "let t : i32 = x + 1; ",
                #22 `}`: "{ let y = x; let t : i32 = x + 1;  }",
            ]
        "#]],
    );
    t(
        "fn f() -> i32 { return 1; } fn g() { let x = f(); g() }",
        expect![[r#"
            [
                #0 `fn`: "fn f() -> i32 { return 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `->`: "() -> i32",
                #5 `i32`: "i32",
                #6 `{`: "() -> i32 { return 1;  }",
                #7 `return`: "return 1",
                #8 `1`: "1" → TypeInference { ty: `Int` },
                #9 `;`: "return 1; ",
                #10 `}`: "{ return 1;  }",
                #11 `fn`: "fn g() { let x = f(); g() }" ✓,
                #12 `g`: "g",
                #13 `(`: `(`,
                #14 `)`: "()",
                #15 `{`: "() { let x = f(); g() }",
                #16 `let`: "let x = f()",
                #17 `x`: "x" → TypeInference { ty: `i32` },
                #18 `=`: "x = f()",
                #19 `f`: "f",
                #20 `(`: "f()" → TypeInference { ty: `i32` },
                #21 `)`: "()",
                #22 `;`: "let x = f(); ",
                #23 `g`: "g",
                #24 `(`: "g()" → TypeInference { ty: `unit` },
                #25 `)`: "()",
                #26 `}`: "{ let x = f(); g() }",
            ]
        "#]],
    );
    t(
        "fn f() -> i32 { return 1; } fn g() { let x = f(); let y = x; }",
        expect![[r#"
            [
                #0 `fn`: "fn f() -> i32 { return 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `->`: "() -> i32",
                #5 `i32`: "i32",
                #6 `{`: "() -> i32 { return 1;  }",
                #7 `return`: "return 1",
                #8 `1`: "1" → TypeInference { ty: `Int` },
                #9 `;`: "return 1; ",
                #10 `}`: "{ return 1;  }",
                #11 `fn`: "fn g() { let x = f(); let y = x;  }" ✓,
                #12 `g`: "g",
                #13 `(`: `(`,
                #14 `)`: "()",
                #15 `{`: "() { let x = f(); let y = x;  }",
                #16 `let`: "let x = f()",
                #17 `x`: "x" → TypeInference { ty: `i32` },
                #18 `=`: "x = f()",
                #19 `f`: "f",
                #20 `(`: "f()" → TypeInference { ty: `i32` },
                #21 `)`: "()",
                #22 `;`: "let x = f(); ",
                #23 `let`: "let y = x",
                #24 `y`: "y" → TypeInference { ty: `i32` },
                #25 `=`: "y = x",
                #26 `x`: "x" → TypeInference { ty: `i32` },
                #27 `;`: "let y = x; ",
                #28 `}`: "{ let x = f(); let y = x;  }",
            ]
        "#]],
    );
    t(
        "fn f(x: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : Float",
                #5 `Float`: "Float",
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x" → TypeInference { ty: `Int` },
                #16 `=`: "x = 1",
                #17 `1`: "1" → TypeInference { ty: `Int` },
                #18 `;`: "let x = 1; ",
                #19 `f`: "f",
                #20 `(`: "f(x)" → TypeInference { ty: `unit` },
                #21 `x`: "x" → TypeInference { ty: `Int` },
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
    t(
        "fn f(a: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(a : Float) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `a`: "a",
                #4 `:`: "a : Float",
                #5 `Float`: "Float",
                #6 `)`: "(a : Float)",
                #7 `{`: "(a : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x" → TypeInference { ty: `Int` },
                #16 `=`: "x = 1",
                #17 `1`: "1" → TypeInference { ty: `Int` },
                #18 `;`: "let x = 1; ",
                #19 `f`: "f",
                #20 `(`: "f(x)" → TypeInference { ty: `unit` },
                #21 `x`: "x" → TypeInference { ty: `Int` },
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TypeDesignation {
    symbol: Symbol,
    ty: Type,
}

fn calc_initial_ty_designations(
    asts: Seq<Option<Ast>>,
    roles: Seq<Option<Role>>,
    symbol_resolutions: Seq<Option<SymbolResolution>>,
    ty_inferences: Seq<Option<TypeInference>>,
    ty_terms: Seq<Option<Type>>,
) -> Seq<Option<TypeDesignation>> {
    let retrieved_symbol_resolutions = symbol_resolutions
        .index(roles.map(|role| match role? {
            Role::LetStmtInner {
                pattern,
                initial_value,
            } => Some(pattern), // ad hoc
            Role::LetStmtTypedVariables { variables, ty } => Some(variables), // ad hoc
            Role::FnParameter {
                fn_ident,
                rank,
                ty,
                fn_ident_idx,
                scope,
            } => Some(fn_ident_idx),
            _ => None,
        }))
        .map(Option::flatten);
    let ty_inferences = ty_inferences
        .index(roles.map(|role| match role? {
            Role::LetStmtInner {
                pattern,
                initial_value,
            } => Some(initial_value),
            _ => None,
        }))
        .map(Option::flatten);
    let retrieved_ty_terms = ty_terms
        .index(roles.map(|role| match role? {
            Role::LetStmtTypedVariables { variables, ty } => Some(ty),
            Role::FnParameter { ty, .. } => Some(ty),
            _ => None,
        }))
        .map(Option::flatten);
    calc_initial_ty_designation.apply(
        retrieved_symbol_resolutions,
        ty_inferences,
        retrieved_ty_terms,
    )
}

fn calc_initial_ty_designation(
    symbol_resolution: Option<SymbolResolution>,
    ty_inference: Option<TypeInference>,
    ty_term: Option<Type>,
) -> Option<TypeDesignation> {
    let symbol = match symbol_resolution? {
        SymbolResolution::Ok(symbol) => symbol,
        SymbolResolution::Err(_) => return None,
    };
    Some(TypeDesignation {
        symbol,
        ty: ty_inference.map(|ti| ti.ty).or(ty_term)?,
    })
}

fn calc_ty_designations_step(
    roles: Seq<Option<Role>>,
    symbol_resolutions: Seq<Option<SymbolResolution>>,
    ty_inferences: Seq<Option<TypeInference>>,
) -> Seq<Option<TypeDesignation>> {
    let retrieved_symbol_resolutions = symbol_resolutions
        .index(roles.map(|role| match role? {
            Role::LetStmtInner {
                pattern,
                initial_value,
            } => Some(pattern),
            Role::FnParameter { fn_ident_idx, .. } => Some(fn_ident_idx),
            _ => None,
        }))
        .map(Option::flatten);
    let ty_inferences = ty_inferences
        .index(roles.map(|role| match role? {
            Role::LetStmtInner {
                pattern,
                initial_value,
            } => Some(initial_value),
            Role::FnParameter {
                fn_ident,
                rank,
                ty,
                fn_ident_idx,
                scope,
            } => None,
            _ => None,
        }))
        .map(Option::flatten);
    calc_ty_designation_step.apply(retrieved_symbol_resolutions, ty_inferences)
}

fn calc_ty_designation_step(
    symbol_resolution: Option<SymbolResolution>,
    ty_inference: Option<TypeInference>,
) -> Option<TypeDesignation> {
    let symbol = match symbol_resolution? {
        SymbolResolution::Ok(symbol) => symbol,
        SymbolResolution::Err(_) => return None,
    };
    Some(TypeDesignation {
        symbol,
        ty: ty_inference?.ty,
    })
}

#[test]
fn calc_ty_designations_works() {}
