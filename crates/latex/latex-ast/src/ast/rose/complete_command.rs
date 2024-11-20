use super::*;
use latex_command::signature::{parameter::LxCommandParameterMode, LxCompleteCommandSignature};
use latex_token::token::{
    name::LxNameTokenData,
    rose::LxRoseDelimiter,
    spec::{LxSpecDelimiter, LxSpecTokenData},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxRoseCompleteCommandArgument {
    pub lcurl_token_idx: LxRoseTokenIdx,
    pub data: LxRoseCompleteCommandArgumentData,
    pub rcurl_token_idx: LxRoseTokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxRoseCompleteCommandArgumentData {
    Name(LxNameTokenIdx, Coword),
    Rose(LxRoseAstIdxRange),
}

impl LxRoseCompleteCommandArgument {
    pub fn lcurl_token_idx(self) -> LxRoseTokenIdx {
        self.lcurl_token_idx
    }

    pub fn data(self) -> LxRoseCompleteCommandArgumentData {
        self.data
    }

    pub fn rcurl_token_idx(self) -> LxRoseTokenIdx {
        self.rcurl_token_idx
    }
}

impl<'a> LxAstParser<'a> {
    pub(super) fn parse_rose_complete_command(
        &mut self,
        command_token_idx: LxRoseTokenIdx,
        command_signature: &LxCompleteCommandSignature,
    ) -> LxRoseAstData {
        let command_path = command_signature.path();
        let mut arguments: SmallVec<[LxRoseCompleteCommandArgument; 2]> = smallvec![];
        let options = self.parse_rose_options();
        for parameter in command_signature.parameters() {
            arguments.push(self.parse_rose_complete_command_argument(parameter.mode()));
        }
        LxRoseAstData::CompleteCommand {
            command_token_idx,
            command_path,
            options,
            arguments,
        }
    }

    fn parse_rose_options(&mut self) -> Option<()> {
        match self.peek_rose_token_data()? {
            LxRoseTokenData::Punctuation(LxRosePunctuation::LeftBox) => (),
            _ => return None,
        }
        let Some((lbox_token_idx, LxRoseTokenData::Punctuation(LxRosePunctuation::LeftBox))) =
            self.next_rose_token()
        else {
            unreachable!("we just peeked a left box")
        };
        // TODO: ad hoc
        while let Some((_, token)) = self.next_spec_token() {
            match token {
                LxSpecTokenData::RightDelimiter(LxSpecDelimiter::Box) => break,
                _ => (),
            }
        }
        Some(())
    }

    fn parse_rose_complete_command_argument(
        &mut self,
        mode: LxCommandParameterMode,
    ) -> LxRoseCompleteCommandArgument {
        let Some((lcurl_token_idx, LxRoseTokenData::LeftDelimiter(LxRoseDelimiter::Curl))) =
            self.next_rose_token()
        else {
            todo!("report errors properly")
        };

        let data = match mode {
            LxCommandParameterMode::Math => todo!(),
            LxCommandParameterMode::Rose => {
                LxRoseCompleteCommandArgumentData::Rose(self.parse_rose_asts())
            }
            LxCommandParameterMode::Name => {
                let Some((name_token_idx, LxNameTokenData::Name(name))) = self.next_name_token()
                else {
                    todo!("report errors properly")
                };
                LxRoseCompleteCommandArgumentData::Name(name_token_idx, name)
            }
            LxCommandParameterMode::SingleLetter => todo!(),
        };
        let Some((rcurl_token_idx, LxRoseTokenData::RightDelimiter(LxRoseDelimiter::Curl))) =
            self.next_rose_token()
        else {
            todo!("report errors properly")
        };
        LxRoseCompleteCommandArgument {
            lcurl_token_idx,
            data,
            rcurl_token_idx,
        }
    }
}
