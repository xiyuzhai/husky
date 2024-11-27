pub mod helpers;
#[cfg(test)]
mod tests;

use super::*;
use latex_command::path::LxCommandPath;
use latex_token::{
    idx::LxLispTokenIdx,
    token::lisp::{
        delimiter::LxLispDelimiter, ident::LxLispIdent, label::LxLispXlabel,
        literal::LxLispLiteral, LxLispTokenData,
    },
};
use smallvec::{smallvec, SmallVec};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxLispAstData {
    Literal(LxLispTokenIdx, LxLispLiteral),
    Ident(LxLispTokenIdx, LxLispIdent),
    Xlabel(LxLispTokenIdx, LxLispXlabel),
    CompleteCommand {
        command_token_idx: LxLispTokenIdx,
        command_path: LxCommandPath,
        arguments: SmallVec<[LxLispCommandArgument; 2]>,
    },
    Parenthesized {
        lpar_token_idx: LxLispTokenIdx,
        asts: LxLispAstIdxRange,
        rpar_token_idx: LxLispTokenIdx,
    },
    BoxedList {
        lbox_token_idx: LxLispTokenIdx,
        items: SmallVec<[LxLispAstIdxRange; 4]>,
        rbox_token_idx: LxLispTokenIdx,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxLispCommandArgument {
    lcurl_token_idx: LxLispTokenIdx,
    data: LxLispCommandArgumentData,
    rcurl_token_idx: LxLispTokenIdx,
}

pub type LxLispAstArena = Arena<LxLispAstData>;
pub type LxLispAstArenaRef<'a> = ArenaRef<'a, LxLispAstData>;
pub type LxLispAstArenaMap<T> = ArenaMap<LxLispAstData, T>;
pub type LxLispAstIdx = ArenaIdx<LxLispAstData>;
pub type LxLispAstIdxRange = ArenaIdxRange<LxLispAstData>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxLispCommandArgumentData {}

impl<'a> LxAstParser<'a> {
    pub fn parse_lisp_asts(&mut self) -> LxLispAstIdxRange {
        let mut asts = vec![];
        while let Some(ast) = self.parse_lisp_ast() {
            asts.push(ast)
        }
        self.alloc_lisp_asts(asts)
    }

    fn parse_lisp_ast(&mut self) -> Option<LxLispAstData> {
        match self.peek_lisp_token_data()? {
            LxLispTokenData::Ident(ident) => (),
            LxLispTokenData::Literal(_) => (),
            LxLispTokenData::Xlabel(label) => (),
            LxLispTokenData::LeftDelimiter(delimiter) => (),
            LxLispTokenData::RightDelimiter(delimiter) => return None,
            LxLispTokenData::Command(command_name) => (),
            LxLispTokenData::Comma => return None,
        }
        let (token_idx, token_data) = self.next_lisp_token()?;
        match token_data {
            LxLispTokenData::Literal(literal) => Some(LxLispAstData::Literal(token_idx, literal)),
            LxLispTokenData::Ident(ident) => Some(LxLispAstData::Ident(token_idx, ident)),
            LxLispTokenData::Xlabel(label) => Some(LxLispAstData::Xlabel(token_idx, label)),
            LxLispTokenData::LeftDelimiter(delimiter) => {
                self.parse_delimited_lisp_ast(token_idx, delimiter)
            }
            LxLispTokenData::RightDelimiter(delimiter) => todo!(),
            LxLispTokenData::Command(command_name) => todo!(),
            LxLispTokenData::Comma => todo!(),
        }
    }

    fn parse_delimited_lisp_ast(
        &mut self,
        token_idx: LxLispTokenIdx,
        delimiter: LxLispDelimiter,
    ) -> Option<LxLispAstData> {
        match delimiter {
            LxLispDelimiter::Parenthesis => self.parse_parenthesized_lisp_ast(token_idx),
            LxLispDelimiter::Box => self.parse_boxed_list_lisp_ast(token_idx),
        }
    }

    fn parse_parenthesized_lisp_ast(
        &mut self,
        lpar_token_idx: LxLispTokenIdx,
    ) -> Option<LxLispAstData> {
        let asts = self.parse_lisp_asts();
        let Some((rpar_token_idx, rpar_token_data)) = self.next_lisp_token() else {
            todo!()
        };
        match rpar_token_data {
            LxLispTokenData::RightDelimiter(LxLispDelimiter::Parenthesis) => (),
            _ => todo!(),
        }
        Some(LxLispAstData::Parenthesized {
            lpar_token_idx,
            asts,
            rpar_token_idx,
        })
    }

    fn parse_boxed_list_lisp_ast(
        &mut self,
        lbox_token_idx: LxLispTokenIdx,
    ) -> Option<LxLispAstData> {
        let mut items: SmallVec<[LxLispAstIdxRange; 4]> = smallvec![self.parse_lisp_asts()];
        let rbox_token_idx = loop {
            match self.next_lisp_token() {
                Some((token_idx, token_data)) => match token_data {
                    LxLispTokenData::RightDelimiter(LxLispDelimiter::Box) => break token_idx,
                    LxLispTokenData::Comma => items.push(self.parse_lisp_asts()),
                    _ => todo!(),
                },
                None => todo!(),
            }
        };
        Some(LxLispAstData::BoxedList {
            lbox_token_idx,
            items,
            rbox_token_idx,
        })
    }
}
