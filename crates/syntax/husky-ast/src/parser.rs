mod defn;
mod indent;
mod stmt;
mod uses;
mod utils;

use crate::*;
use husky_entity_path::path::major_item::connection::DisconnectedConnectionRegistry;
use husky_token::{indent::Indent, *};
use husky_vfs::path::module_path::ModulePath;
use parsec::{HasStreamState, IsStreamParser};
use utils::*;

pub(crate) struct AstParser<'a> {
    db: &'a ::salsa::Db,
    module_path: ModulePath,
    token_sheet: &'a TokenSheetData,
    token_verse_iter: TokenVerseIter<'a>,
    indent: Indent,
    ast_arena: AstArena,
    disambiguator_registry: DisconnectedConnectionRegistry,
    siblings: Vec<AstIdxRange>,
}

impl<'a> HasStreamState for AstParser<'a> {
    type State = TokenVerseIdx;

    fn state(&self) -> Self::State {
        self.token_verse_iter.state()
    }

    fn rollback(&mut self, state: Self::State) {
        self.token_verse_iter.rollback(state)
    }
}

impl<'a> AstParser<'a> {
    pub(crate) fn new(db: &'a ::salsa::Db, module_path: ModulePath) -> Self {
        let token_sheet = db.token_sheet_data(module_path);
        Self {
            db,
            module_path,
            token_sheet,
            token_verse_iter: token_sheet.main_token_verse_iter(),
            indent: Default::default(),
            ast_arena: Default::default(),
            disambiguator_registry: Default::default(),
            siblings: Default::default(),
        }
    }

    pub(crate) fn parse_all(mut self) -> AstSheet {
        let top_level_asts = self.parse_normal_ast_children::<MajorItems>();
        let mut nested_top_level_asts = vec![];
        for seq in self.token_sheet.token_verses().nested_sequences().iter() {
            // todo: refactor such that token_verse_iter is pub(crate)
            self.token_verse_iter = seq.token_verse_iter(self.token_sheet.tokens());
            let indent = self.token_verse_iter.next_token_verse_indent();
            let nested_asts =
                self.with_indent(indent, |slf| slf.parse_normal_ast_children::<FormBody>());
            nested_top_level_asts.push((seq.lcurl(), nested_asts))
        }
        AstSheet::new(
            self.ast_arena,
            top_level_asts,
            nested_top_level_asts,
            self.siblings,
        )
    }

    pub(crate) fn parse_normal_ast_children_indented<C: IsAstChildren>(
        &mut self,
    ) -> Option<AstIdxRange> {
        let range = self.indented(|slf| slf.parse_normal_ast_children::<C>());
        (range.len() > 0).then_some(range)
    }

    fn parse_normal_ast_children<C: IsAstChildren>(&mut self) -> AstIdxRange {
        let mut asts: Vec<AstData> = vec![];
        while let Some(ast) = self.parse_ast::<C>() {
            asts.push(ast)
        }
        let ast_idx_range = self.alloc_asts(asts);
        self.siblings.push(ast_idx_range);
        ast_idx_range
    }

    fn alloc_asts(&mut self, asts: Vec<AstData>) -> AstIdxRange {
        self.ast_arena.alloc_many(asts)
    }

    fn alloc_ast(&mut self, ast: AstData) -> AstIdx {
        self.ast_arena.alloc_one(ast)
    }

    fn parse_ast<C: IsAstChildren>(&mut self) -> Option<AstData> {
        let (token_verse_idx, token_verse, fst, snd) = self
            .token_verse_iter
            .next_token_verse_of_no_less_indent_with_its_first_two_tokens(self.indent())?;
        if token_verse.indent() > self.indent() {
            return Some(AstData::Err {
                token_verse_idx,
                error: OriginalAstError::ExcessiveIndent.into(),
            });
        }
        Some(
            match self.parse_ast_aux::<C>(token_verse_idx, token_verse, fst, snd) {
                Ok(value) => value,
                Err(error) => AstData::Err {
                    token_verse_idx,
                    error,
                },
            },
        )
    }

    fn parse_ast_aux<C: IsAstChildren>(
        &mut self,
        token_verse_idx: TokenVerseIdx,
        _token_verse: TokenVerse,
        fst: TokenData,
        snd: Option<TokenData>,
    ) -> AstResult<AstData> {
        Ok(match fst {
            TokenData::Keyword(kw) => match kw {
                Keyword::Stmt(kw) => self.try_parse_stmt_after_keyword::<C>(token_verse_idx, kw)?,
                Keyword::Todo | Keyword::Sorry | Keyword::Unreachable | Keyword::Pronoun(_) => {
                    self.try_parse_stmt::<C>(token_verse_idx)?
                }
                Keyword::Modifier(_) => Err(OriginalAstError::UnexpectedPattern)?,
                Keyword::Use => self.parse_use_ast(
                    token_verse_idx,
                    VisibilityExpr::new_protected(self.module_path),
                    None,
                ),
                Keyword::Mod | Keyword::Form(_) | Keyword::Trait | Keyword::TypeEntity(_) => self
                    .parse_defn::<C>(
                        token_verse_idx,
                        VisibilityExpr::new_protected(self.module_path),
                        None,
                    ),
                Keyword::Impl => AstData::ImplBlock {
                    token_verse_idx,
                    items: if self.is_trai_impl(token_verse_idx) {
                        // there are no items for marker traits
                        self.try_parse_option::<TraitForTypeItems>()?
                            .map(Into::into)
                    } else {
                        // however, type impl block should always have items
                        Some(
                            self.try_parse_expected::<TypeItems, _>(
                                OriginalAstError::EmptyImplBlock,
                            )?
                            .into(),
                        )
                    },
                },
                Keyword::End(_) => AstData::Err {
                    token_verse_idx,
                    error: OriginalAstError::UnexpectedEndKeywordAsFirstNonCommentToken.into(),
                },
                Keyword::Connection(_) => AstData::Err {
                    token_verse_idx,
                    error: OriginalAstError::UnexpectedConnectionKeywordAsFirstNonCommentToken
                        .into(),
                },
                Keyword::Pub | Keyword::Assoc => self.parse_defn_or_use::<C>(token_verse_idx),
                Keyword::Const => AstData::Err {
                    token_verse_idx,
                    error: OriginalAstError::UnexpectedConst.into(),
                },
                Keyword::Var => AstData::Err {
                    token_verse_idx,
                    error: OriginalAstError::UnexpectedVar.into(),
                },
            },
            TokenData::Punctuation(Punctuation::POUND) => match snd {
                Some(snd) => match snd {
                    TokenData::Punctuation(Punctuation::LBOX) => AstData::Sorc { token_verse_idx },
                    TokenData::Ident(ident) => AstData::Attr {
                        token_verse_idx,
                        ident,
                    },
                    _ => AstData::Err {
                        token_verse_idx,
                        error: OriginalAstError::ExpectedLboxOrIdentAfterPoundForAttrOrSorc(
                            token_verse_idx,
                        )
                        .into(),
                    },
                },
                None => AstData::Err {
                    token_verse_idx,
                    error: OriginalAstError::ExpectedLboxOrIdentAfterPoundForAttrOrSorc(
                        token_verse_idx,
                    )
                    .into(),
                },
            },
            TokenData::Punctuation(_)
            | TokenData::Ident(_)
            | TokenData::Label(_)
            | TokenData::WordOpr(_)
            | TokenData::Literal(_) => self.try_parse_stmt::<C>(token_verse_idx)?,
            TokenData::Error(e) => Err(DerivedAstError::TokenData(e))?,
        })
    }

    fn is_trai_impl(&self, token_verse_idx: TokenVerseIdx) -> bool {
        // ad hoc
        // todo: improve this
        self.token_sheet
            .token_verse_token_stream(token_verse_idx, None)
            .find(|token| *token == &(Keyword::Connection(ConnectionKeyword::For).into()))
            .is_some()
    }

    fn parse_defn_or_use<C: IsAstChildren>(&mut self, token_verse_idx: TokenVerseIdx) -> AstData {
        let mut aux_parser = BasicAuxAstParser::new(
            self.db,
            self.module_path,
            self.token_sheet
                .token_verse_token_stream(token_verse_idx, None),
        );
        let visibility_expr = match aux_parser.parse_visibility_expr() {
            Ok(visibility_expr) => visibility_expr,
            Err(e) => {
                return AstData::Err {
                    token_verse_idx,
                    error: e.into(),
                }
            }
        };
        match aux_parser.peek() {
            Some(TokenData::Keyword(Keyword::Use)) => self.parse_use_ast(
                token_verse_idx,
                visibility_expr,
                Some(aux_parser.finish_with_saved_stream_state()),
            ),
            Some(TokenData::Keyword(_)) => self.parse_defn::<C>(
                token_verse_idx,
                visibility_expr,
                Some(aux_parser.finish_with_saved_stream_state()),
            ),
            _ => AstData::Err {
                token_verse_idx,
                error: OriginalAstError::InvalidAstForDefinitionOrUse.into(),
            },
        }
    }
}
