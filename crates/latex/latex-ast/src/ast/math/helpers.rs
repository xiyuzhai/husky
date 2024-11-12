use super::*;

pub enum LxMathAstChild {
    Ast(LxMathAstIdx),
    CommandArgument(LxMathCommandArgument),
}

impl LxMathAstData {
    pub fn children(&self) -> Vec<LxMathAstChild> {
        match *self {
            LxMathAstData::Delimited { asts, .. } => {
                asts.into_iter().map(LxMathAstChild::Ast).collect()
            }
            LxMathAstData::Attach {
                base, ref scripts, ..
            } => [(base)]
                .into_iter()
                .chain(scripts.iter().map(|&(_, ast)| ast))
                .map(LxMathAstChild::Ast)
                .collect(),
            LxMathAstData::PlainLetter(_, _) => vec![],
            LxMathAstData::StyledLetter { .. } => vec![],
            LxMathAstData::Punctuation(_, _) => vec![],
            LxMathAstData::Digit(_, _) => vec![],
            LxMathAstData::TextEdit { ref buffer } => vec![],
            LxMathAstData::CompleteCommand {
                command_token_idx,
                command_path,
                ref arguments,
            } => arguments
                .iter()
                .copied()
                .map(LxMathAstChild::CommandArgument)
                .collect(),
            LxMathAstData::Environment { asts, .. } => match asts {
                LxAstIdxRange::Math(asts) => asts.into_iter().map(LxMathAstChild::Ast).collect(),
                LxAstIdxRange::Rose(asts) => todo!(),
            },
        }
    }
}
