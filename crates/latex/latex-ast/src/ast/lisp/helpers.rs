use super::*;

pub enum LxLispAstChild {
    LispAst(LxLispAstIdx),
    Item(LxLispAstIdxRange),
}

impl LxLispAstData {
    pub fn children(&self) -> Vec<LxLispAstChild> {
        match *self {
            LxLispAstData::Ident(_, _)
            | LxLispAstData::Literal(_, _)
            | LxLispAstData::Xlabel(_, _) => vec![],
            LxLispAstData::CompleteCommand {
                command_token_idx,
                command_path,
                ref arguments,
            } => todo!(),
            LxLispAstData::Parenthesized {
                lpar_token_idx,
                asts,
                rpar_token_idx,
            } => asts.into_iter().map(LxLispAstChild::LispAst).collect(),
            LxLispAstData::BoxedList {
                lbox_token_idx,
                ref items,
                rbox_token_idx,
            } => items.iter().copied().map(LxLispAstChild::Item).collect(),
        }
    }
}
