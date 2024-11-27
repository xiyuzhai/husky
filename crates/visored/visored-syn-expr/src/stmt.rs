#[cfg(test)]
mod tests;

use crate::{
    builder::{ToVdSyn, VdSynExprBuilder},
    sentence::{VdSynSentenceIdx, VdSynSentenceIdxRange},
    symbol::builder::VdSynSymbolBuilder,
    *,
};
use coword::Coword;
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use latex_ast::ast::{
    root::LxRootAstIdxRange,
    rose::{LxRoseAstData, LxRoseAstIdx, LxRoseAstIdxRange},
    LxAstIdxRange,
};
use latex_environment::signature::LxEnvironmentSignature;
use latex_token::idx::{LxNameTokenIdx, LxRoseTokenIdx, LxTokenIdxRange};
use std::iter::Peekable;
use visored_global_resolution::resolution::command::VdCompleteCommandGlobalResolution;

pub enum VdSynStmtData {
    Paragraph(VdSynSentenceIdxRange),
    Environment {
        begin_command_token_idx: LxRoseTokenIdx,
        environment_signature: LxEnvironmentSignature,
        stmts: VdSynStmtIdxRange,
        end_rcurl_token_idx: LxRoseTokenIdx,
    },
}

pub type VdSynStmtArena = Arena<VdSynStmtData>;
pub type VdSynStmtArenaRef<'a> = ArenaRef<'a, VdSynStmtData>;
pub type VdSynStmtIdx = ArenaIdx<VdSynStmtData>;
pub type VdSynStmtIdxRange = ArenaIdxRange<VdSynStmtData>;
pub type VdSynStmtMap<T> = ArenaMap<VdSynStmtData, T>;
pub type VdSynStmtOrderedMap<T> = ArenaOrderedMap<VdSynStmtData, T>;

impl ToVdSyn<VdSynStmtIdxRange> for (LxTokenIdxRange, LxRoseAstIdxRange) {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynStmtIdxRange {
        self.1.to_vd_syn(builder)
    }
}

impl ToVdSyn<VdSynStmtIdxRange> for LxRoseAstIdxRange {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynStmtIdxRange {
        builder.build_stmts(self)
    }
}

impl<'db> VdSynExprBuilder<'db> {
    fn build_stmts(&mut self, asts: LxRoseAstIdxRange) -> VdSynStmtIdxRange {
        let mut asts = asts.into_iter().peekable();
        self.build_stmt_aux(&mut asts)
    }

    pub(crate) fn build_stmt_aux(
        &mut self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> VdSynStmtIdxRange {
        let mut stmts: Vec<VdSynStmtData> = Vec::new();
        while let Some(stmt) = self.build_stmt(asts) {
            stmts.push(stmt);
        }
        self.alloc_stmts(stmts)
    }

    fn build_stmt(
        &mut self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> Option<VdSynStmtData> {
        // stop on new division
        if self.peek_new_division(asts).is_some() {
            return None;
        }

        let ast_idx = asts.next()?;
        Some(match self.ast_arena()[ast_idx] {
            LxRoseAstData::TextEdit { ref buffer } => todo!(),
            LxRoseAstData::Word(token_idx, word) => self.build_paragraph(token_idx, word, asts),
            LxRoseAstData::Punctuation(token_idx, punctuation) => {
                todo!("punctuation: {}", punctuation)
            }
            LxRoseAstData::Math { .. } => todo!(),
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
            } => self.build_environment(
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
            ),
            LxRoseAstData::NewParagraph(_) => self.build_stmt(asts)?,
        })
    }

    fn build_paragraph(
        &mut self,
        token_idx: LxRoseTokenIdx,
        word: Coword,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> VdSynStmtData {
        let mut sentences = vec![self.parse_sentence(token_idx, word, asts)];
        loop {
            // stop on new division
            if self.peek_new_division(asts).is_some() {
                break;
            }
            let Some(ast_idx) = asts.next() else { break };
            match self.ast_arena()[ast_idx] {
                LxRoseAstData::TextEdit { .. } => todo!(),
                LxRoseAstData::Word(lx_rose_token_idx, coword) => {
                    sentences.push(self.parse_sentence(lx_rose_token_idx, coword, asts));
                }
                LxRoseAstData::Punctuation(lx_rose_token_idx, lx_rose_punctuation) => todo!(),
                LxRoseAstData::Math {
                    left_delimiter_token_idx: left_dollar_token_idx,
                    math_asts,
                    right_delimiter_token_idx: right_dollar_token_idx,
                } => todo!(),
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
                } => {
                    use husky_print_utils::{p, DisplayIt};
                    p!(command_path);
                    todo!()
                }
                LxRoseAstData::Environment { .. } => todo!(),
                LxRoseAstData::NewParagraph(_) => todo!(),
            }
        }
        VdSynStmtData::Paragraph(self.alloc_sentences(sentences))
    }

    fn build_environment(
        &mut self,
        begin_command_token_idx: LxRoseTokenIdx,
        begin_lcurl_token_idx: LxRoseTokenIdx,
        begin_environment_name_token_idx: LxNameTokenIdx,
        begin_rcurl_token_idx: LxRoseTokenIdx,
        asts: LxAstIdxRange,
        end_command_token_idx: LxRoseTokenIdx,
        end_lcurl_token_idx: LxRoseTokenIdx,
        end_environment_name_token_idx: LxNameTokenIdx,
        end_rcurl_token_idx: LxRoseTokenIdx,
        environment_signature: LxEnvironmentSignature,
    ) -> VdSynStmtData {
        VdSynStmtData::Environment {
            begin_command_token_idx,
            environment_signature,
            stmts: match asts {
                LxAstIdxRange::Math(arena_idx_range) => todo!(),
                LxAstIdxRange::Root(arena_idx_range) => todo!(),
                LxAstIdxRange::Rose(asts) => asts.to_vd_syn(self),
                LxAstIdxRange::Lisp(arena_idx_range) => todo!(),
            },
            end_rcurl_token_idx,
        }
    }
}

pub enum VdSynStmtChild {
    Sentence(VdSynSentenceIdx),
    Stmt(VdSynStmtIdx),
}

impl VdSynStmtData {
    pub(crate) fn children(&self) -> Vec<VdSynStmtChild> {
        match self {
            VdSynStmtData::Paragraph(sentences) => sentences
                .into_iter()
                .map(VdSynStmtChild::Sentence)
                .collect(),
            VdSynStmtData::Environment { stmts, .. } => {
                stmts.into_iter().map(VdSynStmtChild::Stmt).collect()
            }
        }
    }
}

impl<'db> VdSynSymbolBuilder<'db> {
    pub(crate) fn build_stmt_aux(&mut self, stmt: VdSynStmtIdx) {
        match self.stmt_arena()[stmt] {
            VdSynStmtData::Paragraph(sentences) => self.build_sentences(sentences),
            VdSynStmtData::Environment {
                environment_signature,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => self.build_stmts(stmts),
        }
    }
}
