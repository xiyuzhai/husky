pub mod complete_command;
pub mod environment;
pub mod helpers;
#[cfg(test)]
pub mod tests;

use self::environment::LxRootEnvironmentAstData;
use super::*;
use coword::Coword;
use latex_command::{
    path::{LxCommandName, LxCommandPath},
    signature::{
        parameter::LxCommandParameterMode, LxCommandSignature, LxCompleteCommandSignature,
    },
};
use latex_environment::signature::LxEnvironmentSignature;
use latex_token::{
    idx::{LxNameTokenIdx, LxRootTokenIdx},
    token::{
        name::LxNameTokenData,
        root::{LxRootDelimiter, LxRootTokenData},
        spec::{LxSpecDelimiter, LxSpecTokenData},
    },
};
use smallvec::{smallvec, SmallVec};

#[derive(Debug, PartialEq, Eq)]
pub enum LxRootAstData {
    CompleteCommand {
        command_token_idx: LxRootTokenIdx,
        command_path: LxCommandPath,
        // TODO: ad hoc
        options: Option<()>,
        arguments: SmallVec<[LxRootCompleteCommandArgument; 2]>,
    },
    Environment {
        begin_command_token_idx: LxRootTokenIdx,
        begin_lcurl_token_idx: LxRootTokenIdx,
        begin_environment_name_token_idx: LxNameTokenIdx,
        begin_rcurl_token_idx: LxRootTokenIdx,
        asts: LxAstIdxRange,
        end_command_token_idx: LxRootTokenIdx,
        end_lcurl_token_idx: LxRootTokenIdx,
        end_environment_name_token_idx: LxNameTokenIdx,
        end_rcurl_token_idx: LxRootTokenIdx,
        environment_signature: LxEnvironmentSignature,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxRootCompleteCommandArgument {
    lcurl_token_idx: LxRootTokenIdx,
    data: LxRootCommandArgumentData,
    rcurl_token_idx: LxRootTokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxRootCommandArgumentData {
    Name(LxNameTokenIdx, Coword),
}

pub type LxRootAstArena = Arena<LxRootAstData>;
pub type LxRootAstArenaRef<'a> = ArenaRef<'a, LxRootAstData>;
pub type LxRootAstIdx = ArenaIdx<LxRootAstData>;
pub type LxRootAstIdxRange = ArenaIdxRange<LxRootAstData>;
pub type LxRootAstArenaMap<T> = ArenaMap<LxRootAstData, T>;

impl LxRootCompleteCommandArgument {
    pub fn lcurl_token_idx(self) -> LxRootTokenIdx {
        self.lcurl_token_idx
    }

    pub fn data(self) -> LxRootCommandArgumentData {
        self.data
    }

    pub fn rcurl_token_idx(self) -> LxRootTokenIdx {
        self.rcurl_token_idx
    }
}

impl<'a> LxAstParser<'a> {
    pub fn parse_root_asts(&mut self) -> LxRootAstIdxRange {
        let mut asts = vec![];
        while let Some(ast) = self.parse_root_ast() {
            asts.push(ast)
        }
        self.alloc_root_asts(asts)
    }

    pub fn parse_root_ast(&mut self) -> Option<LxRootAstData> {
        match self.peek_root_token_data()? {
            LxRootTokenData::RightDelimiter(_) => return None,
            // TODO: this is a hack
            LxRootTokenData::Command(command_name)
                if command_name == self.command_path_menu().end.name() =>
            {
                return None
            }
            _ => (),
        };
        let (token_idx, token) = self.next_root_token()?;
        match token {
            LxRootTokenData::Command(command_name) => {
                self.parse_root_command(token_idx, command_name)
            }
            LxRootTokenData::LeftDelimiter(root_delimiter) => todo!(),
            LxRootTokenData::RightDelimiter(root_delimiter) => todo!(),
        }
    }

    fn parse_root_command(
        &mut self,
        command_token_idx: LxRootTokenIdx,
        command_name: LxCommandName,
    ) -> Option<LxRootAstData> {
        let Some(command_signature) = self.command_signature_table().signature(command_name) else {
            todo!(
                "handle command `{}` not found in command signature table",
                command_name
            )
        };
        Some(match *command_signature {
            LxCommandSignature::Complete(ref command_signature) => {
                self.parse_root_complete_command(command_token_idx, command_signature)
            }
            LxCommandSignature::MathLetterStyle(style) => {
                todo!()
            }
            LxCommandSignature::Begin => self.parse_root_environment(command_token_idx),
            LxCommandSignature::End => todo!(),
        })
    }
}
