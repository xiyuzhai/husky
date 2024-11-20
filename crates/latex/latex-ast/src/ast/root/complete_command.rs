use super::*;

impl<'a> LxAstParser<'a> {
    pub(super) fn parse_root_complete_command(
        &mut self,
        command_token_idx: LxRootTokenIdx,
        command_signature: &LxCompleteCommandSignature,
    ) -> LxRootAstData {
        let command_path = command_signature.path();
        let mut arguments: SmallVec<[LxRootCompleteCommandArgument; 2]> = smallvec![];
        let options = self.parse_root_options();
        for parameter in command_signature.parameters() {
            arguments.push(self.parse_root_complete_command_argument(parameter.mode()));
        }
        LxRootAstData::CompleteCommand {
            command_token_idx,
            command_path,
            options,
            arguments,
        }
    }

    fn parse_root_options(&mut self) -> Option<()> {
        match self.peek_root_token_data()? {
            LxRootTokenData::LeftDelimiter(LxRootDelimiter::Box) => (),
            _ => return None,
        }
        let Some((lbox_token_idx, LxRootTokenData::LeftDelimiter(LxRootDelimiter::Box))) =
            self.next_root_token()
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

    fn parse_root_complete_command_argument(
        &mut self,
        mode: LxCommandParameterMode,
    ) -> LxRootCompleteCommandArgument {
        let Some((lcurl_token_idx, LxRootTokenData::LeftDelimiter(LxRootDelimiter::Curl))) =
            self.next_root_token()
        else {
            todo!("report errors properly")
        };

        let data = match mode {
            LxCommandParameterMode::Math => todo!(),
            LxCommandParameterMode::Rose => todo!(),
            LxCommandParameterMode::Name => {
                let Some((name_token_idx, LxNameTokenData::Name(name))) = self.next_name_token()
                else {
                    todo!("report errors properly")
                };
                LxRootCommandArgumentData::Name(name_token_idx, name)
            }
            LxCommandParameterMode::SingleLetter => todo!(),
        };
        let Some((rcurl_token_idx, LxRootTokenData::RightDelimiter(LxRootDelimiter::Curl))) =
            self.next_root_token()
        else {
            todo!("report errors properly")
        };
        LxRootCompleteCommandArgument {
            lcurl_token_idx,
            data,
            rcurl_token_idx,
        }
    }
}
