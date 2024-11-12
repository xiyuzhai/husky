use super::*;
use crate::{rank::Rank, symbol::Symbol, token::ident::Ident};
use cybertron::seq::Seq;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TypeSignature {
    pub key: TypeSignatureKey,
    pub ty: Type,
}

impl TypeSignature {
    pub fn key(self) -> TypeSignatureKey {
        self.key
    }

    pub fn ty(&self) -> Type {
        self.ty
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeSignatureKey {
    FnParameter { fn_ident: Ident, rank: Rank },
    FnOutput { fn_ident: Ident },
    StructField { ty_ident: Ident, field_ident: Ident },
}

pub(super) fn calc_ty_signatures(
    asts: Seq<Option<Ast>>,
    roles: Seq<Option<Role>>,
    ty_terms: Seq<Option<Type>>,
) -> Seq<Option<TypeSignature>> {
    calc_ty_signature.apply(roles, ty_terms)
}

fn calc_ty_signature(role: Option<Role>, ty_term: Option<Type>) -> Option<TypeSignature> {
    let key = match role? {
        Role::FnParameterType { fn_ident, rank } => {
            TypeSignatureKey::FnParameter { fn_ident, rank }
        }
        Role::StructFieldType {
            ty_ident,
            field_ident,
        } => TypeSignatureKey::StructField {
            ty_ident,
            field_ident,
        },
        Role::FnOutputType { fn_ident } => TypeSignatureKey::FnOutput { fn_ident },
        Role::FnParameters {
            fn_ident,
            has_return_ty: false,
            scope,
        } => {
            let key = TypeSignatureKey::FnOutput { fn_ident };
            let ty = Type::new_ident(Ident::new("unit"));
            return Some(TypeSignature { key, ty });
        }
        _ => return None,
    };
    // put it here!
    let ty = ty_term?;
    Some(TypeSignature { key, ty })
}

#[cfg(test)]
fn t(input: &str, expect: Expect) {
    use scope::infer_scopes;
    use signature::calc_ty_signatures;
    use term::calc_ty_terms;

    let (tokens, pre_asts, asts) =
        calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
    let scopes = infer_scopes(asts, 10);
    let roles = calc_roles(asts, scopes, 10);
    let ranks = calc_ranks(asts);
    let ty_terms = calc_ty_terms(asts, roles, 10);
    let ty_signatures = calc_ty_signatures(asts, roles, ty_terms);
    expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ty_signatures));
}

#[test]
fn ty_signatures_works() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "struct A { x: i32, y: Vec[i32] }",
        expect![[r#"
            [
                #0 `struct`: "struct A { x : i32, y : Vec[i32] }" ✓,
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `x`: "x",
                #4 `:`: "x : i32",
                #5 `i32`: "i32" → TypeSignature { key: StructField { ty_ident: `A`, field_ident: `x` }, ty: `i32` },
                #6 `,`: "x : i32, ",
                #7 `y`: "y",
                #8 `:`: "y : Vec[i32]",
                #9 `Vec`: "Vec",
                #10 `[`: "Vec[i32]" → TypeSignature { key: StructField { ty_ident: `A`, field_ident: `y` }, ty: `Vec[i32]` },
                #11 `i32`: "i32",
                #12 `]`: "[i32]",
                #13 `}`: "{ x : i32, y : Vec[i32] }",
            ]
        "#]],
    );
    t(
        "fn f(a: i32, b: Option[f32]) -> f32 { return 1 }",
        expect![[r#"
            [
                #0 `fn`: "fn f(a : i32, b : Option[f32]) -> f32 { return 1 }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `a`: "a",
                #4 `:`: "a : i32",
                #5 `i32`: "i32" → TypeSignature { key: FnParameter { fn_ident: `f`, rank: Rank(0) }, ty: `i32` },
                #6 `,`: "a : i32, ",
                #7 `b`: "b",
                #8 `:`: "b : Option[f32]",
                #9 `Option`: "Option",
                #10 `[`: "Option[f32]" → TypeSignature { key: FnParameter { fn_ident: `f`, rank: Rank(1) }, ty: `Option[f32]` },
                #11 `f32`: "f32",
                #12 `]`: "[f32]",
                #13 `)`: "(a : i32, b : Option[f32])",
                #14 `->`: "(a : i32, b : Option[f32]) -> f32",
                #15 `f32`: "f32" → TypeSignature { key: FnOutput { fn_ident: `f` }, ty: `f32` },
                #16 `{`: "(a : i32, b : Option[f32]) -> f32 { return 1 }",
                #17 `return`: "return 1",
                #18 `1`: "1",
                #19 `}`: "{ return 1 }",
            ]
        "#]],
    );
}
