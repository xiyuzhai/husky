use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntityKindKeywordGroup {
    // todo: remove mod
    Mod(ModToken),
    // `fn`
    Fn(FormFnToken),
    // `const fn`
    ConstFn(ConstToken, FormFnToken),
    // `static fn`
    StaticFn(StaticToken, FormFnToken),
    // `static const fn`
    StaticConstFn(StaticToken, ConstToken, FormFnToken),
    // `var`
    Val(VarToken),
    // `gn`
    Gn(GnToken),
    //
    GeneralDef(GeneralDefToken),
    // Type
    TypeEntity(TypeEntityToken),
    // Type
    Type(TypeToken),
    Trait(TraitToken),
    Visual(VisualToken),
    Memo(MemoToken),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormFnToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConstToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StaticToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralDefToken {
    Def(DefToken),
    Lemma(LemmaToken),
    Theorem(TheoremToken),
    Function(FunctionToken),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefToken {
    token_idx: TokenIdx,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LemmaToken {
    token_idx: TokenIdx,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoremToken {
    token_idx: TokenIdx,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeEntityToken {
    keyword: TypeEntityKeyword,
    token_idx: TokenIdx,
}
impl TypeEntityToken {
    pub fn type_kind(self) -> TypeKind {
        // MOM
        match self.keyword {
            TypeEntityKeyword::Extern => TypeKind::Extern,
            TypeEntityKeyword::Struct => TypeKind::Struct,
            TypeEntityKeyword::Enum => TypeKind::Enum,
            TypeEntityKeyword::Record => TypeKind::Record,
            TypeEntityKeyword::Structure => TypeKind::Structure,
            TypeEntityKeyword::Inductive => TypeKind::Inductive,
        }
    }

    pub fn keyword(self) -> TypeEntityKeyword {
        self.keyword
    }

    pub fn token_idx(self) -> TokenIdx {
        self.token_idx
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraitToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VarToken {
    token_idx: TokenIdx,
}

impl VarToken {
    pub fn token_idx(&self) -> TokenIdx {
        self.token_idx
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GnToken {
    token_idx: TokenIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VisualToken {
    token_idx: TokenIdx,
}

impl<'a, Context> parsec::ParseFromStream<Context> for EntityKindKeywordGroup
where
    Context: TokenParseContext<'a>,
{
    type Error = TokenError;

    fn parse_from_without_guaranteed_rollback(ctx: &mut Context) -> TokenResult<Option<Self>> {
        let token_stream: &mut TokenStream<'a> = &mut ctx.borrow_mut();
        let Some((token_idx, token)) = token_stream.next_indexed() else {
            return Ok(None)
        };
        let kw = match token {
            Token::Keyword(kw) => kw,
            Token::Error(error) => Err(error)?,
            _ => return Ok(None),
        };
        match kw {
            Keyword::Form(kw) => match kw {
                FormKeyword::Def => todo!(),
                FormKeyword::Fn => Ok(Some(EntityKindKeywordGroup::Fn(FormFnToken { token_idx }))),
                FormKeyword::Theorem => Ok(Some(EntityKindKeywordGroup::GeneralDef(
                    GeneralDefToken::Theorem(TheoremToken { token_idx }),
                ))),
                FormKeyword::Lemma => todo!(),
                FormKeyword::Proposition => todo!(),
                FormKeyword::Type => {
                    Ok(Some(EntityKindKeywordGroup::Type(TypeToken { token_idx })))
                }
                FormKeyword::Const => todo!(),
                FormKeyword::Val => Ok(Some(EntityKindKeywordGroup::Val(VarToken { token_idx }))),
                FormKeyword::Gn => Ok(Some(EntityKindKeywordGroup::Gn(GnToken { token_idx }))),
                FormKeyword::Constexpr => todo!(),
                FormKeyword::Memo => {
                    Ok(Some(EntityKindKeywordGroup::Memo(MemoToken { token_idx })))
                }
            },
            Keyword::TypeEntity(keyword) => {
                Ok(Some(EntityKindKeywordGroup::TypeEntity(TypeEntityToken {
                    keyword,
                    token_idx,
                })))
            }
            Keyword::Stmt(_) => todo!(),
            Keyword::Main => Ok(None),
            Keyword::Mod => Ok(Some(EntityKindKeywordGroup::Mod(ModToken { token_idx }))),
            Keyword::Visual => Ok(Some(EntityKindKeywordGroup::Visual(VisualToken {
                token_idx,
            }))),
            Keyword::Trait => Ok(Some(EntityKindKeywordGroup::Trait(TraitToken {
                token_idx,
            }))),
            Keyword::Static => match token_stream.peek() {
                Some(Token::Keyword(Keyword::Form(FormKeyword::Fn))) => {
                    token_stream.next();
                    Ok(Some(EntityKindKeywordGroup::StaticFn(
                        StaticToken { token_idx },
                        FormFnToken {
                            token_idx: token_idx + 1,
                        },
                    )))
                }
                Some(Token::Keyword(Keyword::Form(FormKeyword::Const))) => todo!(),
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }
}