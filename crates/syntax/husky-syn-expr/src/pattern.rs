mod contract;
mod region;
mod symbol;

pub use self::region::*;
pub use self::symbol::*;

use super::*;
use husky_coword::Ident;
use husky_entity_kind::MajorFormKind;
use husky_entity_path::path::{major_item::ty::TypePath, ty_variant::TypeVariantPath, ItemPath};
use idx_arena::{map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange};
use parsec::{IsStreamParser, PunctuatedSmallList, TryParseOptionFromStream};
use std::ops::ControlFlow;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum SynPatternData {
    /// example: `1`
    Literal {
        regional_token_idx: RegionalTokenIdx,
        literal: LiteralTokenData,
    },
    /// example: `a`
    Ident {
        symbol_modifier_tokens: Option<EphemSymbolModifierRegionalTokens>,
        ident_token: IdentRegionalToken,
    },
    /// example: `A::B`
    UnitTypeVariant {
        path_expr_idx: SynPrincipalEntityPathExprIdx,
        path: TypeVariantPath,
    },
    /// example: `(a, b)`
    Tuple {
        lpar: LparRegionalToken,
        fields: PunctuatedSmallList<SynPatternIdx, CommaRegionalToken, SynExprError, true, 3>,
        rpar: RparRegionalToken,
    },
    TupleStruct {
        name: TypePath,
        lpar: LparRegionalToken,
        fields: PunctuatedSmallList<SynPatternIdx, CommaRegionalToken, SynExprError, true, 3>,
        rpar: RparRegionalToken,
    },
    TupleTypeVariant {
        path_expr_idx: SynPrincipalEntityPathExprIdx,
        path: TypeVariantPath,
        lpar: LparRegionalToken,
        fields: PunctuatedSmallList<
            /* ad hoc */ SynPatternComponent,
            CommaRegionalToken,
            SynExprError,
            true,
            3,
        >,
        rpar: RparRegionalToken,
    },
    /// example: `C { .. }`
    Props {
        name: Option<ItemPath>,
        fields: PunctuatedSmallList<FieldSynPatternData, CommaRegionalToken, SynExprError, true, 3>,
    },
    /// example: `A | B | C { .. }`
    OneOf {
        options:
            PunctuatedSmallList<SynPatternComponent, VerticalRegionalToken, SynExprError, false, 3>,
    },
    /// example: `x @ 1..9`
    Binding {
        ident_token: IdentRegionalToken,
        asperand_token: AtRegionalToken,
        /// example: `1..9`
        src: SynPatternIdx,
    },
    /// example: `1..9`
    Range {
        start: SynPatternIdx,
        dot_dot_token: DotDotRegionalToken,
        end: SynPatternIdx,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldSynPatternData {
    ident: IdentRegionalToken,
    colon: ColonRegionalToken,
    pattern: SynPatternComponent,
}

pub type SynPatternArena = Arena<SynPatternData>;
pub type SynPatternIdx = ArenaIdx<SynPatternData>;
pub type SynPatternIdxRange = ArenaIdxRange<SynPatternData>;
pub type SynPatternMap<V> = ArenaMap<SynPatternData, V>;
pub type SynPatternOrderedMap<V> = ArenaOrderedMap<SynPatternData, V>;

/// irreducible against `|`
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SynPatternComponent(SynPatternIdx);

impl SynPatternComponent {
    pub fn syn_pattern(self) -> SynPatternIdx {
        self.0
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for SynPatternComponent
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        parser: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let symbol_modifier_tokens: Option<EphemSymbolModifierRegionalTokens> =
            parser.try_parse_option()?;
        let Some((regional_token_idx, token_data)) = parser.next_indexed() else {
            return Ok(None);
        };
        let db = parser.db();
        let expr = match parser.disambiguate_token(regional_token_idx, token_data) {
            ControlFlow::Continue(resolved_token) => {
                match resolved_token {
                    DisambiguatedTokenData::Literal(regional_token_idx, literal) => {
                        Some(SynPatternData::Literal {
                            regional_token_idx,
                            literal,
                        })
                    }
                    DisambiguatedTokenData::IdentifiableEntityPath(syn_expr) => match syn_expr {
                        ItemPathExpr::Principal {
                            path_expr_idx,
                            opt_path,
                        } => match opt_path {
                            Some(path) => match path {
                                // modules and major items will be overriden by pattern symbol
                                PrincipalEntityPath::Module(_) => parse_overriding_ident_pattern(
                                    parser,
                                    path_expr_idx,
                                    symbol_modifier_tokens,
                                ),
                                PrincipalEntityPath::MajorItem(path) => match path {
                                    MajorItemPath::Type(_) => todo!(),
                                    MajorItemPath::Trait(_) => todo!(),
                                    MajorItemPath::Form(path) => match path.kind(db) {
                                        MajorFormKind::Ritchie(_) | MajorFormKind::Val => {
                                            parse_overriding_ident_pattern(
                                                parser,
                                                path_expr_idx,
                                                symbol_modifier_tokens,
                                            )
                                        }
                                        MajorFormKind::TypeAlias => todo!(),
                                        MajorFormKind::TypeVar => todo!(),
                                        MajorFormKind::Conceptual => todo!(),
                                        MajorFormKind::StaticMut => todo!(),
                                        MajorFormKind::StaticVar => todo!(),
                                        MajorFormKind::Compterm => todo!(),
                                    },
                                },
                                PrincipalEntityPath::TypeVariant(path) => {
                                    if let Some(lpar) =
                                        parser.try_parse_option::<LparRegionalToken>()?
                                    {
                                        let fields = parser.try_parse()?;
                                        let rpar = parser.try_parse_expected(
                                            OriginalSynExprError::ExpectedRpar,
                                        )?;
                                        Some(SynPatternData::TupleTypeVariant {
                                            path_expr_idx,
                                            path,
                                            lpar,
                                            fields,
                                            rpar,
                                        })
                                    } else if let Some(_) =
                                        parser.try_parse_option::<InlineLcurlRegionalToken>()?
                                    {
                                        todo!("struct variant");
                                    } else {
                                        if symbol_modifier_tokens.is_some() {
                                            todo!()
                                        }
                                        Some(SynPatternData::UnitTypeVariant {
                                            path_expr_idx,
                                            path,
                                        })
                                    }
                                }
                            },
                            None => todo!(),
                        },
                        ItemPathExpr::AssocItem { .. } => todo!(),
                    },
                    DisambiguatedTokenData::InheritedVariable {
                        regional_token_idx,
                        ident,
                        ..
                    }
                    | DisambiguatedTokenData::CurrentVariable {
                        regional_token_idx,
                        ident,
                        ..
                    }
                    | DisambiguatedTokenData::UnrecognizedIdent {
                        regional_token_idx,
                        ident,
                    } => Some(SynPatternData::Ident {
                        symbol_modifier_tokens,
                        ident_token: IdentRegionalToken::new(ident, regional_token_idx),
                    }),
                    DisambiguatedTokenData::SelfValue(_) => todo!(),
                    DisambiguatedTokenData::LeftDelimiter(_, _) => todo!(),
                    _ => None,
                }
            }
            ControlFlow::Break(_) => None,
        };
        let Some(expr) = expr else {
            if let Some(_) = symbol_modifier_tokens {
                todo!()
            } else {
                return Ok(None);
            }
        };
        Ok(Some(SynPatternComponent(
            parser.context.borrow_mut().alloc_pattern(expr),
        )))
    }
}

fn parse_overriding_ident_pattern<'a, C>(
    parser: &mut SynExprParser<'a, C>,
    path_expr_idx: SynPrincipalEntityPathExprIdx,
    symbol_modifier_tokens: Option<EphemSymbolModifierRegionalTokens>,
) -> Option<SynPatternData>
where
    C: IsSynExprContext<'a>,
{
    match parser.context().syn_principal_entity_path_expr_arena()[path_expr_idx] {
        SynPrincipalEntityPathExpr::Root {
            path_name_token, ..
        } => match path_name_token {
            PathNameRegionalToken::Ident(ident_token) => Some(SynPatternData::Ident {
                symbol_modifier_tokens,
                ident_token,
            }),
            PathNameRegionalToken::CrateRootMod(_) => todo!(),
            PathNameRegionalToken::SelfMod(_) => todo!(),
            PathNameRegionalToken::SuperMod(_) => todo!(),
        },
        SynPrincipalEntityPathExpr::Subitem { .. } => todo!(),
    }
}

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    fn try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
        self: &mut SynExprParser<'a, C>,
        root_kind: SynPatternRootKind,
    ) -> SynExprResult<Option<SynPatternRoot>> {
        let punctuated_patterns = self.try_parse::<PunctuatedSmallList<
            SynPatternComponent,
            VerticalRegionalToken,
            SynExprError,
            false,
            3,
        >>()?;
        match punctuated_patterns.elements().len() {
            0 => Ok(None),
            1 => Ok(Some(SynPatternRoot::new(
                root_kind,
                punctuated_patterns.elements()[0].0,
                self.context_mut(),
            ))),
            _ => {
                let expr = SynPatternData::OneOf {
                    options: punctuated_patterns,
                };
                Ok(Some(SynPatternRoot::new(
                    root_kind,
                    self.context_mut().alloc_pattern(expr),
                    self.context_mut(),
                )))
            }
        }
    }
}

/// # parenate

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParenateParameterSynPatternRoot {
    syn_pattern_idx: SynPatternIdx,
}

impl ParenateParameterSynPatternRoot {
    pub fn syn_pattern_idx(&self) -> SynPatternIdx {
        self.syn_pattern_idx
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for ParenateParameterSynPatternRoot
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        sp: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let Some(root) = sp
            .try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
                SynPatternRootKind::Parenate,
            )?
        else {
            return Ok(None);
        };
        Ok(Some(ParenateParameterSynPatternRoot {
            syn_pattern_idx: root.syn_pattern_idx(),
        }))
    }
}

/// # closure parameter

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ClosureSynPatternRoot {
    syn_pattern_idx: SynPatternIdx,
}

impl ClosureSynPatternRoot {
    pub fn syn_pattern_idx(&self) -> SynPatternIdx {
        self.syn_pattern_idx
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for ClosureSynPatternRoot
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        sp: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let Some(root) = sp
            .try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
                SynPatternRootKind::Closure,
            )?
        else {
            return Ok(None);
        };
        Ok(Some(ClosureSynPatternRoot {
            syn_pattern_idx: root.syn_pattern_idx(),
        }))
    }
}

// let variable

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LetPatternSynExprRoot {
    syn_pattern_idx: SynPatternIdx,
}

impl LetPatternSynExprRoot {
    pub fn syn_pattern_idx(&self) -> SynPatternIdx {
        self.syn_pattern_idx
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for LetPatternSynExprRoot
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        sp: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let Some(root) = sp
            .try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
                SynPatternRootKind::Let,
            )?
        else {
            return Ok(None);
        };
        Ok(Some(LetPatternSynExprRoot {
            syn_pattern_idx: root.syn_pattern_idx(),
        }))
    }
}

// case

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaseSynPatternRoot {
    syn_pattern_idx: SynPatternIdx,
}

impl CaseSynPatternRoot {
    pub fn syn_pattern_idx(&self) -> SynPatternIdx {
        self.syn_pattern_idx
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for CaseSynPatternRoot
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        sp: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let Some(root) = sp
            .try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
                SynPatternRootKind::Case,
            )?
        else {
            return Ok(None);
        };
        Ok(Some(CaseSynPatternRoot {
            syn_pattern_idx: root.syn_pattern_idx(),
        }))
    }
}

// be

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BeSynPatternRoot {
    syn_pattern_idx: SynPatternIdx,
}

impl BeSynPatternRoot {
    pub fn syn_pattern_idx(&self) -> SynPatternIdx {
        self.syn_pattern_idx
    }
}

impl<'a, C> TryParseOptionFromStream<SynExprParser<'a, C>> for BeSynPatternRoot
where
    C: IsSynExprContext<'a>,
{
    type Error = SynExprError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        sp: &mut SynExprParser<'a, C>,
    ) -> Result<Option<Self>, Self::Error> {
        let Some(root) = sp
            .try_parse_option_syn_pattern_root_from_stream_without_guaranteed_rollback(
                SynPatternRootKind::Be,
            )?
        else {
            return Ok(None);
        };
        Ok(Some(BeSynPatternRoot {
            syn_pattern_idx: root.syn_pattern_idx(),
        }))
    }
}
