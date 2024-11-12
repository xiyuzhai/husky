pub mod helpers;
#[cfg(test)]
mod tests;

use super::*;
use husky_coword::Coword;
use latex_command::{
    path::LxCommandPath,
    signature::{parameter::LxCommandParameterMode, LxCommandSignature},
};
use latex_environment::{
    path::{LxEnvironmentName, LxEnvironmentPath},
    signature::LxEnvironmentSignature,
};
use latex_math_letter::letter::styled::LxMathLetterStyle;
use latex_token::{
    data::{
        code::LxCodeTokenData,
        math::{digit::LxMathDigit, LxMathDelimiter},
    },
    idx::{LxCodeTokenIdx, LxMathTokenIdx, LxTokenIdxRange},
};
use smallvec::{smallvec, SmallVec};

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxMathAstData {
    PlainLetter(LxMathTokenIdx, LxMathLetter),
    StyledLetter {
        style_command_token_idx: LxMathTokenIdx,
        style_lcurl_token_idx: LxMathTokenIdx,
        plain_letter_token_idx: LxMathTokenIdx,
        style_rcurl_token_idx: LxMathTokenIdx,
        style: LxMathLetterStyle,
        styled_letter: LxMathLetter,
    },
    Punctuation(LxMathTokenIdx, LxMathPunctuation),
    Digit(LxMathTokenIdx, LxMathDigit),
    /// not obtained through parsing, but through ui
    TextEdit {
        buffer: String,
    },
    Attach {
        base: LxMathAstIdx,
        scripts: Vec<(LxScriptKind, LxMathAstIdx)>,
    },
    Delimited {
        left_delimiter_token_idx: LxMathTokenIdx,
        left_delimiter: LxMathDelimiter,
        asts: LxMathAstIdxRange,
        right_delimiter_token_idx: LxMathTokenIdx,
        right_delimiter: LxMathDelimiter,
    },
    CompleteCommand {
        command_token_idx: LxMathTokenIdx,
        command_path: LxCommandPath,
        arguments: SmallVec<[LxMathCommandArgument; 2]>,
    },
    Environment {
        begin_command_token_idx: LxMathTokenIdx,
        begin_lcurl_token_idx: LxMathTokenIdx,
        begin_environment_name_token_idx: LxCodeTokenIdx,
        begin_rcurl_token_idx: LxMathTokenIdx,
        asts: LxAstIdxRange,
        end_command_token_idx: LxMathTokenIdx,
        end_lcurl_token_idx: LxMathTokenIdx,
        end_environment_name_token_idx: LxCodeTokenIdx,
        end_rcurl_token_idx: LxMathTokenIdx,
        environment_signature: LxEnvironmentSignature,
    },
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxMathCommandArgument {
    lcurl_token_idx: LxMathTokenIdx,
    data: LxMathCommandArgumentData,
    rcurl_token_idx: LxMathTokenIdx,
}

impl LxMathCommandArgument {
    pub fn lcurl_token_idx(&self) -> LxMathTokenIdx {
        self.lcurl_token_idx
    }

    pub fn data(&self) -> &LxMathCommandArgumentData {
        &self.data
    }

    pub fn rcurl_token_idx(&self) -> LxMathTokenIdx {
        self.rcurl_token_idx
    }

    pub fn asts_token_idx_range(&self) -> LxTokenIdxRange {
        ((*self.lcurl_token_idx + 1)..*self.rcurl_token_idx).into()
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxMathCommandArgumentData {
    Math(LxMathAstIdxRange),
    Rose(LxRoseAstIdxRange),
    Letter(LxMathTokenIdx, LxMathLetter),
}

pub type LxMathAstArena = Arena<LxMathAstData>;
pub type LxMathAstArenaRef<'a> = ArenaRef<'a, LxMathAstData>;
pub type LxMathAstArenaMap<T> = ArenaMap<LxMathAstData, T>;
pub type LxMathAstIdx = ArenaIdx<LxMathAstData>;
pub type LxMathAstIdxRange = ArenaIdxRange<LxMathAstData>;

impl<'a> LxAstParser<'a> {
    pub(super) fn parse_math_asts(&mut self) -> LxMathAstIdxRange {
        let mut asts = vec![];
        while let Some(ast) = self.parse_math_ast() {
            asts.push(ast)
        }
        self.alloc_math_asts(asts)
    }

    fn parse_math_ast(&mut self) -> Option<LxMathAstData> {
        let mut ast = self.parse_atomic_math_ast()?;
        while let Some(token_data) = self.peek_math_token_data() {
            match token_data {
                // TODO include more cases, like \limits
                LxMathTokenData::Subscript | LxMathTokenData::Superscript => {
                    let (idx, token) = self.next_math_token().unwrap();
                    ast = match ast {
                        LxMathAstData::Attach { .. } => ast,
                        base => {
                            let base = self.alloc_math_ast(base);
                            LxMathAstData::Attach {
                                base,
                                scripts: Default::default(),
                            }
                            .into()
                        }
                        _ => todo!(),
                    };
                    let LxMathAstData::Attach {
                        ref mut scripts, ..
                    } = ast
                    else {
                        unreachable!()
                    };
                    let script_kind = match token {
                        LxMathTokenData::Subscript => LxScriptKind::Subscript,
                        LxMathTokenData::Superscript => LxScriptKind::Superscript,
                        _ => todo!(),
                    };
                    let ast = match self.parse_atomic_math_ast() {
                        Some(new_subscript) => self.alloc_math_ast(new_subscript),
                        None => todo!("err: expected subscript"),
                    };
                    // check that the script kind is not already present
                    if scripts.iter().copied().any(|(kind, _)| kind == script_kind) {
                        todo!("err: script kind already present")
                    }
                    scripts.push((script_kind, ast));
                }
                _ => break,
            }
        }
        Some(ast)
    }

    fn parse_atomic_math_ast(&mut self) -> Option<LxMathAstData> {
        match self.peek_math_token_data()? {
            LxMathTokenData::RightDelimiter(_) | LxMathTokenData::MathModeEnd => return None,
            LxMathTokenData::Command(Ok(command_name))
                if command_name == self.command_path_menu().end.name() =>
            {
                return None
            }
            _ => (),
        };
        let (idx, token) = self.next_math_token()?;
        Some(match token {
            LxMathTokenData::Command(command_name) => {
                let command_name = match command_name {
                    Ok(command_name) => command_name,
                    Err(e) => todo!("{e}"),
                };
                let Some(command_signature) =
                    self.command_signature_table().signature(command_name)
                else {
                    use salsa::DisplayWithDb;
                    todo!(
                        "handle command `{}` not found in command signature table",
                        command_name.display(self.db())
                    )
                };
                match *command_signature {
                    LxCommandSignature::Complete(ref command_signature) => {
                        let command_path = command_signature.path();
                        let mut arguments: SmallVec<[LxMathCommandArgument; 2]> = smallvec![];
                        for parameter in command_signature.parameters() {
                            arguments.push(self.parse_command_argument(parameter.mode())?);
                        }
                        LxMathAstData::CompleteCommand {
                            command_token_idx: idx,
                            command_path,
                            arguments,
                        }
                    }
                    LxCommandSignature::Begin => self.parse_environment(idx),
                    LxCommandSignature::End => unreachable!(),
                    LxCommandSignature::MathLetterStyle(style) => {
                        self.parse_styled_letter(idx, style)
                    }
                }
            }
            LxMathTokenData::LeftDelimiter(delimiter) => self.parse_delimited(idx, delimiter),
            LxMathTokenData::RightDelimiter(_) => unreachable!(),
            LxMathTokenData::Letter(letter) => LxMathAstData::PlainLetter(idx, letter),
            LxMathTokenData::Punctuation(opr) => LxMathAstData::Punctuation(idx, opr), // it's not constructed into a tree yet in the ast stage
            LxMathTokenData::Digit(digit) => LxMathAstData::Digit(idx, digit),
            LxMathTokenData::Other(c) => todo!("c: {}", c),
            LxMathTokenData::Subscript => todo!(),
            LxMathTokenData::Superscript => todo!(),
            LxMathTokenData::Error(_) => todo!(),
            LxMathTokenData::MathModeEnd => unreachable!(),
        })
    }

    fn parse_command_argument(
        &mut self,
        mode: LxCommandParameterMode,
    ) -> Option<LxMathCommandArgument> {
        match self.peek_math_token_data()? {
            LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl) => (),
            _ => return None,
        }
        let (lcurl_token_idx, LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl)) =
            self.next_math_token()?
        else {
            unreachable!()
        };
        let data = match mode {
            LxCommandParameterMode::Math => LxMathCommandArgumentData::Math(self.parse_math_asts()),
            LxCommandParameterMode::Rose => LxMathCommandArgumentData::Rose(self.parse_rose_asts()),
            LxCommandParameterMode::SingleLetter => todo!(),
        };
        let (rcurl_token_idx, LxMathTokenData::RightDelimiter(LxMathDelimiter::Curl)) =
            self.next_math_token()?
        else {
            todo!("report error properly")
        };
        Some(LxMathCommandArgument {
            lcurl_token_idx,
            data,
            rcurl_token_idx,
        })
    }

    // here we differ from the latex syntax, we see all possible delimiters as latex delimiters
    fn parse_delimited(
        &mut self,
        left_delimiter_token_idx: LxMathTokenIdx,
        left_delimiter: LxMathDelimiter,
    ) -> LxMathAstData {
        let asts = self.parse_math_asts();
        let Some((idx, token)) = self.next_math_token() else {
            todo!()
        };
        match token {
            LxMathTokenData::Command(_) => todo!(),
            LxMathTokenData::LeftDelimiter(_) => todo!(),
            LxMathTokenData::RightDelimiter(right_delimiter) => LxMathAstData::Delimited {
                left_delimiter_token_idx,
                left_delimiter,
                asts,
                right_delimiter_token_idx: idx,
                right_delimiter,
            },
            LxMathTokenData::Letter(_) => todo!(),
            LxMathTokenData::Punctuation(_) => todo!(),
            LxMathTokenData::Digit(_) => todo!(),
            LxMathTokenData::Other(_) => todo!(),
            LxMathTokenData::Subscript => todo!(),
            LxMathTokenData::Superscript => todo!(),
            LxMathTokenData::Error(_) => todo!(),
            LxMathTokenData::MathModeEnd => todo!(),
        }
    }

    fn parse_environment(&mut self, begin_command_token_idx: LxMathTokenIdx) -> LxMathAstData {
        let Some((begin_lcurl_token_idx, begin_lcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match begin_lcurl_token {
            LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl) => {}
            _ => todo!(),
        };
        let Some((begin_environment_name_token_idx, begin_environment_name_token)) =
            self.next_code_token()
        else {
            todo!()
        };
        let LxCodeTokenData::Word(begin_environment_name) = begin_environment_name_token else {
            todo!()
        };
        let Some((begin_rcurl_token_idx, begin_rcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match begin_rcurl_token {
            LxMathTokenData::RightDelimiter(LxMathDelimiter::Curl) => (),
            _ => todo!(),
        };
        let begin_environment_name = LxEnvironmentName::new(begin_environment_name);
        let Some(environment_signature) = self
            .environment_signature_table()
            .signature(begin_environment_name)
        else {
            todo!()
        };
        if !environment_signature.allowed_in_math() {
            todo!()
        }
        let asts = match environment_signature.body_mode() {
            LxMode::Math => self.parse_math_asts().into(),
            LxMode::Rose => self.parse_rose_asts().into(),
        };
        let Some((end_command_token_idx, end_command_token)) = self.next_math_token() else {
            todo!()
        };
        match end_command_token {
            LxMathTokenData::Command(Ok(command_name))
                if command_name == self.command_path_menu().end.name() => {}
            _ => todo!(),
        };
        let Some((end_lcurl_token_idx, end_lcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match end_lcurl_token {
            LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl) => {}
            _ => todo!(),
        };
        let Some((end_environment_name_token_idx, end_environment_name_token)) =
            self.next_code_token()
        else {
            todo!()
        };
        let LxCodeTokenData::Word(end_environment_name) = end_environment_name_token else {
            todo!()
        };
        let Some((end_rcurl_token_idx, end_rcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match end_rcurl_token {
            LxMathTokenData::RightDelimiter(LxMathDelimiter::Curl) => (),
            _ => todo!(),
        };
        if begin_environment_name.coword() != end_environment_name {
            todo!()
        }
        LxMathAstData::Environment {
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

    fn parse_styled_letter(
        &mut self,
        style_command_token_idx: LxMathTokenIdx,
        style: LxMathLetterStyle,
    ) -> LxMathAstData {
        let Some((style_lcurl_token_idx, style_lcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match style_lcurl_token {
            LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl) => (),
            _ => todo!(),
        };
        let Some((plain_letter_token_idx, plain_letter_token)) = self.next_math_token() else {
            todo!()
        };
        let LxMathTokenData::Letter(plain_letter) = plain_letter_token else {
            todo!()
        };
        let Some((style_rcurl_token_idx, style_rcurl_token)) = self.next_math_token() else {
            todo!()
        };
        match style_rcurl_token {
            LxMathTokenData::RightDelimiter(LxMathDelimiter::Curl) => (),
            _ => todo!(),
        };
        let styled_letter = match style.apply(plain_letter) {
            Ok(styled_letter) => styled_letter,
            Err(e) => todo!("{}", e),
        };
        LxMathAstData::StyledLetter {
            style_command_token_idx,
            style_lcurl_token_idx,
            plain_letter_token_idx,
            style_rcurl_token_idx,
            style,
            styled_letter,
        }
    }
}
