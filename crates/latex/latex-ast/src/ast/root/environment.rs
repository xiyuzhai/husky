use latex_environment::path::LxEnvironmentName;

use super::*;

#[derive(Debug, PartialEq, Eq)]
pub enum LxRootEnvironmentAstData {}

impl<'a> LxAstParser<'a> {
    pub(super) fn parse_root_environment(
        &mut self,
        begin_command_token_idx: LxRootTokenIdx,
    ) -> LxRootAstData {
        let Some((begin_lcurl_token_idx, begin_lcurl_token)) = self.next_root_token() else {
            todo!()
        };
        match begin_lcurl_token {
            LxRootTokenData::LeftDelimiter(LxRootDelimiter::Curl) => {}
            _ => todo!(),
        };
        let Some((begin_environment_name_token_idx, begin_environment_name_token)) =
            self.next_name_token()
        else {
            todo!()
        };
        let LxNameTokenData::Name(begin_environment_name) = begin_environment_name_token else {
            todo!()
        };
        let Some((begin_rcurl_token_idx, begin_rcurl_token)) = self.next_root_token() else {
            todo!()
        };
        match begin_rcurl_token {
            LxRootTokenData::RightDelimiter(LxRootDelimiter::Curl) => (),
            _ => todo!(),
        };
        let begin_environment_name = LxEnvironmentName::new(begin_environment_name);
        let Some(environment_signature) = self
            .environment_signature_table()
            .signature(begin_environment_name)
        else {
            todo!()
        };
        if !environment_signature.allowed_in_root() {
            todo!()
        }
        let asts = match environment_signature.body_mode() {
            LxMode::Root => self.parse_root_asts().into(),
            LxMode::Rose => self.parse_rose_asts().into(),
            LxMode::Name => todo!(),
            LxMode::Lisp => todo!(),
            LxMode::Math => todo!(),
        };
        let Some((end_command_token_idx, end_command_token)) = self.next_root_token() else {
            todo!()
        };
        match end_command_token {
            LxRootTokenData::Command(command_name)
                if command_name == self.command_path_menu().end.name() => {}
            _ => todo!(),
        };
        let Some((end_lcurl_token_idx, end_lcurl_token)) = self.next_root_token() else {
            todo!()
        };
        match end_lcurl_token {
            LxRootTokenData::LeftDelimiter(LxRootDelimiter::Curl) => {}
            _ => todo!(),
        };
        let Some((end_environment_name_token_idx, end_environment_name_token)) =
            self.next_name_token()
        else {
            todo!()
        };
        let LxNameTokenData::Name(end_environment_name) = end_environment_name_token else {
            todo!()
        };
        let Some((end_rcurl_token_idx, end_rcurl_token)) = self.next_root_token() else {
            todo!()
        };
        match end_rcurl_token {
            LxRootTokenData::RightDelimiter(LxRootDelimiter::Curl) => (),
            _ => todo!(),
        };
        if begin_environment_name.coword() != end_environment_name {
            todo!()
        }
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
        }
    }
}
