//! means the prose mode
pub mod complete_command;
pub mod delimited;
pub mod environment;
pub mod helpers;
#[cfg(test)]
pub mod tests;

use self::{complete_command::*, delimited::*, environment::*};
use super::*;
use helpers::LxRoseAstChild;
use husky_coword::Coword;
use latex_command::{
    path::{LxCommandName, LxCommandPath},
    signature::LxCommandSignature,
};
use latex_environment::signature::LxEnvironmentSignature;
use latex_rose_punctuation::LxRosePunctuation;
use latex_token::{
    idx::{LxNameTokenIdx, LxRoseTokenIdx},
    token::rose::{LxRoseDelimiter, LxRoseEmbeddedMathDelimiter, LxRoseTokenData},
};
use smallvec::{smallvec, SmallVec};

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxRoseAstData {
    TextEdit {
        buffer: String,
    },
    Word(LxRoseTokenIdx, Coword),
    Punctuation(LxRoseTokenIdx, LxRosePunctuation),
    /// it might be '$' or '$$' or '\[' but we don't care for now
    Math {
        left_delimiter_token_idx: LxRoseTokenIdx,
        math_asts: LxMathAstIdxRange,
        right_delimiter_token_idx: LxRoseTokenIdx,
    },
    Delimited {
        left_delimiter_token_idx: LxRoseTokenIdx,
        left_delimiter: LxRoseDelimiter,
        asts: LxRoseAstIdxRange,
        right_delimiter_token_idx: LxRoseTokenIdx,
        right_delimiter: LxRoseDelimiter,
    },
    CompleteCommand {
        command_token_idx: LxRoseTokenIdx,
        command_path: LxCommandPath,
        options: Option<()>,
        arguments: SmallVec<[LxRoseCompleteCommandArgument; 2]>,
    },
    Environment {
        begin_command_token_idx: LxRoseTokenIdx,
        begin_lcurl_token_idx: LxRoseTokenIdx,
        begin_environment_name_token_idx: LxNameTokenIdx,
        begin_rcurl_token_idx: LxRoseTokenIdx,
        environment_signature: LxEnvironmentSignature,
        asts: LxAstIdxRange,
        end_command_token_idx: LxRoseTokenIdx,
        end_lcurl_token_idx: LxRoseTokenIdx,
        end_environment_name_token_idx: LxNameTokenIdx,
        end_rcurl_token_idx: LxRoseTokenIdx,
    },
    NewParagraph(LxRoseTokenIdx),
}

pub type LxRoseAstArena = Arena<LxRoseAstData>;
pub type LxRoseAstArenaRef<'a> = ArenaRef<'a, LxRoseAstData>;
pub type LxRoseAstArenaMap<T> = ArenaMap<LxRoseAstData, T>;
pub type LxRoseAstIdx = ArenaIdx<LxRoseAstData>;
pub type LxRoseAstIdxRange = ArenaIdxRange<LxRoseAstData>;

impl LxRoseAstData {
    pub fn children(&self) -> Vec<LxRoseAstChild> {
        match *self {
            LxRoseAstData::TextEdit { .. } => vec![],
            LxRoseAstData::Word(_, _) => vec![],
            LxRoseAstData::Punctuation(_, _) => vec![],
            LxRoseAstData::Math { math_asts, .. } => math_asts
                .into_iter()
                .map(|ast| LxRoseAstChild::MathAst(ast))
                .collect(),
            LxRoseAstData::Delimited {
                left_delimiter_token_idx,
                left_delimiter,
                asts,
                right_delimiter_token_idx,
                right_delimiter,
            } => todo!(),
            LxRoseAstData::CompleteCommand {
                command_token_idx,
                command_path,
                options,
                ref arguments,
            } => todo!(),
            LxRoseAstData::Environment { asts, .. } => match asts {
                LxAstIdxRange::Math(asts) => {
                    asts.into_iter().map(LxRoseAstChild::MathAst).collect()
                }
                LxAstIdxRange::Rose(asts) => todo!(),
                LxAstIdxRange::Lisp(asts) => todo!(),
                LxAstIdxRange::Root(arena_idx_range) => todo!(),
            },
            LxRoseAstData::NewParagraph(_) => vec![],
        }
    }
}

impl<'a> LxAstParser<'a> {
    pub(crate) fn parse_rose_asts(&mut self) -> LxRoseAstIdxRange {
        let mut asts = vec![];
        while let Some(ast) = self.parse_rose_ast() {
            asts.push(ast)
        }
        self.alloc_rose_asts(asts)
    }

    fn parse_rose_ast(&mut self) -> Option<LxRoseAstData> {
        match self.peek_rose_token_data()? {
            // TODO: this is a hack
            LxRoseTokenData::Command(command_name)
                if command_name == self.command_path_menu().end.name() =>
            {
                return None
            }
            LxRoseTokenData::RightDelimiter(_) => return None,
            _ => (),
        };
        let (token_idx, token) = self.next_rose_token()?;
        Some(match token {
            LxRoseTokenData::Word(word) => LxRoseAstData::Word(token_idx, word),
            LxRoseTokenData::Command(command_name) => {
                self.parse_rose_command(token_idx, command_name)
            }
            LxRoseTokenData::EmbeddedMathDelimiter(left_delimiter) => {
                self.parse_embedded_math(token_idx, left_delimiter)
            }
            LxRoseTokenData::Nat32(_) => todo!(),
            LxRoseTokenData::NewParagraph => LxRoseAstData::NewParagraph(token_idx),
            LxRoseTokenData::Punctuation(lx_rose_punctuation) => {
                LxRoseAstData::Punctuation(token_idx, lx_rose_punctuation)
            }
            LxRoseTokenData::LeftDelimiter(lx_rose_delimiter) => todo!(),
            LxRoseTokenData::RightDelimiter(lx_rose_delimiter) => todo!(),
        })
    }

    fn parse_rose_command(
        &mut self,
        command_token_idx: LxRoseTokenIdx,
        command_name: LxCommandName,
    ) -> LxRoseAstData {
        let Some(command_signature) = self.command_signature_table().signature(command_name) else {
            use salsa::DisplayWithDb;
            todo!(
                "handle command `{}` not found in command signature table",
                command_name.display(self.db())
            )
        };
        match *command_signature {
            LxCommandSignature::Complete(ref command_signature) => {
                self.parse_rose_complete_command(command_token_idx, command_signature)
            }
            LxCommandSignature::Begin => self.parse_rose_environment(command_token_idx),
            LxCommandSignature::End => unreachable!(),
            LxCommandSignature::MathLetterStyle(style) => {
                todo!("report error")
            }
        }
    }

    fn parse_embedded_math(
        &mut self,
        left_dollar_token_idx: LxRoseTokenIdx,
        left_delimiter: LxRoseEmbeddedMathDelimiter,
    ) -> LxRoseAstData {
        match left_delimiter {
            LxRoseEmbeddedMathDelimiter::Dollar => (),
            LxRoseEmbeddedMathDelimiter::DollarDollar => (),
            LxRoseEmbeddedMathDelimiter::EscapedLbox => (),
            LxRoseEmbeddedMathDelimiter::EscapedRbox => todo!(),
        }

        let math_asts = self.parse_math_asts();

        match self.next_rose_token() {
            Some((
                right_dollar_token_idx,
                LxRoseTokenData::EmbeddedMathDelimiter(right_delimiter),
            )) => {
                if !left_delimiter.is_matching(right_delimiter) {
                    todo!("report error")
                }
                LxRoseAstData::Math {
                    left_delimiter_token_idx: left_dollar_token_idx,
                    math_asts,
                    right_delimiter_token_idx: right_dollar_token_idx,
                }
            }
            _ => todo!(),
        }
    }
}
