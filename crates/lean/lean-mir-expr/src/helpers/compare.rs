use crate::expr::{application::LnMirFunc, LnMirExprArenaRef, LnMirExprData, LnMirExprIdx};

pub fn ln_mir_expr_deep_eq(a: LnMirExprIdx, b: LnMirExprIdx, arena: LnMirExprArenaRef) -> bool {
    if a == b {
        return true;
    }
    match (arena[a].data(), arena[b].data()) {
        (LnMirExprData::Literal(a), LnMirExprData::Literal(b)) => a == b,
        (LnMirExprData::ItemPath(a), LnMirExprData::ItemPath(b)) => a == b,
        (LnMirExprData::Variable { ident: a }, LnMirExprData::Variable { ident: b }) => a == b,
        (
            &LnMirExprData::Lambda {
                parameters: ref a_params,
                body: a_body,
            },
            &LnMirExprData::Lambda {
                parameters: ref b_params,
                body: b_body,
            },
        ) => todo!(),
        (
            &LnMirExprData::Application {
                function: a_fn,
                arguments: a_args,
            },
            &LnMirExprData::Application {
                function: b_fn,
                arguments: b_args,
            },
        ) => {
            ln_mir_fn_deep_eq(a_fn, b_fn, arena)
                && a_args.len() == b_args.len()
                && a_args
                    .into_iter()
                    .zip(b_args.into_iter())
                    .all(|(a, b)| ln_mir_expr_deep_eq(a, b, arena))
        }
        (LnMirExprData::Sorry, LnMirExprData::Sorry) => true,
        (LnMirExprData::By { tactics: a_tactics }, LnMirExprData::By { tactics: b_tactics }) => {
            todo!()
        }
        _ => false,
    }
}

fn ln_mir_fn_deep_eq(a: LnMirFunc, b: LnMirFunc, arena: LnMirExprArenaRef) -> bool {
    match a {
        LnMirFunc::PrefixOpr { .. }
        | LnMirFunc::BinaryOpr { .. }
        | LnMirFunc::SuffixOpr { .. }
        | LnMirFunc::InSet
        | LnMirFunc::Iff => a == b,
        LnMirFunc::Expr(a) => {
            let LnMirFunc::Expr(b) = b else { return false };
            ln_mir_expr_deep_eq(a, b, arena)
        }
    }
}
