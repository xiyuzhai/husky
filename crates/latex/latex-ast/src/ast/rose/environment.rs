use latex_environment::path::LxEnvironmentName;
use latex_token::token::name::LxNameTokenData;

use super::*;

#[derive(Debug, PartialEq, Eq)]
pub enum LxRoseEnvironmentAstData {}

impl<'a> LxAstParser<'a> {
    pub(super) fn parse_rose_environment(
        &mut self,
        begin_command_token_idx: LxRoseTokenIdx,
    ) -> LxRoseAstData {
        let Some((begin_lcurl_token_idx, begin_lcurl_token)) = self.next_rose_token() else {
            todo!()
        };
        match begin_lcurl_token {
            LxRoseTokenData::LeftDelimiter(LxRoseDelimiter::Curl) => {}
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
        let Some((begin_rcurl_token_idx, begin_rcurl_token)) = self.next_rose_token() else {
            todo!()
        };
        match begin_rcurl_token {
            LxRoseTokenData::RightDelimiter(LxRoseDelimiter::Curl) => (),
            _ => todo!(),
        };
        let begin_environment_name = LxEnvironmentName::new(begin_environment_name);
        let Some(environment_signature) = self
            .environment_signature_table()
            .signature(begin_environment_name)
        else {
            todo!()
        };
        if !environment_signature.allowed_in_rose() {
            todo!()
        }
        let asts = match environment_signature.body_mode() {
            LxMode::Lisp => self.parse_lisp_asts().into(),
            LxMode::Math => self.parse_math_asts().into(),
            LxMode::Name => todo!(),
            LxMode::Root => self.parse_root_asts().into(),
            LxMode::Rose => self.parse_rose_asts().into(),
        };
        let Some((end_command_token_idx, end_command_token)) = self.next_rose_token() else {
            todo!()
        };
        match end_command_token {
            LxRoseTokenData::Command(command_name)
                if command_name == self.command_path_menu().end.name() => {}
            _ => todo!(),
        };
        let Some((end_lcurl_token_idx, end_lcurl_token)) = self.next_rose_token() else {
            todo!()
        };
        match end_lcurl_token {
            LxRoseTokenData::LeftDelimiter(LxRoseDelimiter::Curl) => {}
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
        let Some((end_rcurl_token_idx, end_rcurl_token)) = self.next_rose_token() else {
            todo!()
        };
        match end_rcurl_token {
            LxRoseTokenData::RightDelimiter(LxRoseDelimiter::Curl) => (),
            _ => todo!(),
        };
        if begin_environment_name.coword() != end_environment_name {
            todo!()
        }
        LxRoseAstData::Environment {
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
