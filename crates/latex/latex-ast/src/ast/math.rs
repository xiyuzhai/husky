pub mod complete_command;
pub mod environment;
pub mod helpers;
#[cfg(test)]
mod tests;

use super::*;
use coword::Coword;
use latex_command::{
    path::{LxCommandName, LxCommandPath},
    signature::{
        parameter::LxCommandParameterMode, LxCommandSignature, LxCompleteCommandSignature,
    },
};
use latex_environment::{
    path::{LxEnvironmentName, LxEnvironmentPath},
    signature::LxEnvironmentSignature,
};
use latex_math_letter::letter::styled::LxMathLetterStyle;
use latex_token::{
    idx::{LxMathTokenIdx, LxNameTokenIdx, LxTokenIdxRange},
    token::{
        math::{digit::LxMathDigit, LxMathDelimiter},
        name::LxNameTokenData,
    },
};
use smallvec::{smallvec, SmallVec};

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
        arguments: SmallVec<[LxMathCompleteCommandArgument; 2]>,
    },
    Environment {
        begin_command_token_idx: LxMathTokenIdx,
        begin_lcurl_token_idx: LxMathTokenIdx,
        begin_environment_name_token_idx: LxNameTokenIdx,
        begin_rcurl_token_idx: LxMathTokenIdx,
        asts: LxAstIdxRange,
        end_command_token_idx: LxMathTokenIdx,
        end_lcurl_token_idx: LxMathTokenIdx,
        end_environment_name_token_idx: LxNameTokenIdx,
        end_rcurl_token_idx: LxMathTokenIdx,
        environment_signature: LxEnvironmentSignature,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxMathCompleteCommandArgument {
    lcurl_token_idx: LxMathTokenIdx,
    data: LxMathCommandArgumentData,
    rcurl_token_idx: LxMathTokenIdx,
}

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

impl LxMathCompleteCommandArgument {
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

impl<'a> LxAstParser<'a> {
    pub fn parse_math_asts(&mut self) -> LxMathAstIdxRange {
        let mut asts = vec![];
        while let Some(ast) = self.parse_math_ast() {
            asts.push(ast)
        }
        self.alloc_math_asts(asts)
    }

    pub fn parse_math_ast(&mut self) -> Option<LxMathAstData> {
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
            // TODO: this is a hack
            LxMathTokenData::Command(command_name)
                if command_name == self.command_path_menu().end.name() =>
            {
                return None
            }
            _ => (),
        };
        let (token_idx, token) = self.next_math_token()?;
        Some(match token {
            LxMathTokenData::Command(command_name) => {
                self.parse_math_command(token_idx, command_name)
            }
            LxMathTokenData::LeftDelimiter(delimiter) => self.parse_delimited(token_idx, delimiter),
            LxMathTokenData::RightDelimiter(_) => unreachable!(),
            LxMathTokenData::Letter(letter) => LxMathAstData::PlainLetter(token_idx, letter),
            LxMathTokenData::Punctuation(opr) => LxMathAstData::Punctuation(token_idx, opr), // it's not constructed into a tree yet in the ast stage
            LxMathTokenData::Digit(digit) => LxMathAstData::Digit(token_idx, digit),
            LxMathTokenData::Other(c) => todo!("c: {:?}", c),
            LxMathTokenData::Subscript => todo!(),
            LxMathTokenData::Superscript => todo!(),
            LxMathTokenData::Error(_) => todo!(),
            LxMathTokenData::MathModeEnd => unreachable!(),
        })
    }

    fn parse_math_command(
        &mut self,
        command_token_idx: LxMathTokenIdx,
        command_name: LxCommandName,
    ) -> LxMathAstData {
        let Some(command_signature) = self.command_signature_table().signature(command_name) else {
            todo!(
                "handle command `{}` not found in command signature table",
                command_name
            )
        };
        match *command_signature {
            LxCommandSignature::Complete(ref command_signature) => {
                self.parse_math_complete_command(command_token_idx, command_signature)
            }
            LxCommandSignature::Begin => self.parse_math_environment(command_token_idx),
            LxCommandSignature::End => unreachable!(),
            LxCommandSignature::MathLetterStyle(style) => {
                self.parse_styled_letter(command_token_idx, style)
            }
        }
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
