use super::*;

pub enum LxRootAstChild {
    CommandArgument(LxRootCompleteCommandArgument),
    RoseAst(LxRoseAstIdx),
}

impl LxRootAstData {
    pub fn children(&self) -> Vec<LxRootAstChild> {
        match *self {
            LxRootAstData::CompleteCommand { ref arguments, .. } => arguments
                .iter()
                .copied()
                .map(LxRootAstChild::CommandArgument)
                .collect(),
            LxRootAstData::Environment {
                begin_command_token_idx,
                begin_lcurl_token_idx,
                begin_environment_name_token_idx,
                begin_rcurl_token_idx,
                asts,
                end_command_token_idx,
                end_lcurl_token_idx,
                end_environment_name_token_idx,
                end_rcurl_token_idx,
                environment_signature,
            } => match asts {
                LxAstIdxRange::Math(asts) => todo!(),
                LxAstIdxRange::Root(asts) => todo!(),
                LxAstIdxRange::Lisp(asts) => todo!(),
                LxAstIdxRange::Rose(asts) => {
                    asts.into_iter().map(LxRootAstChild::RoseAst).collect()
                }
            },
        }
    }
}
