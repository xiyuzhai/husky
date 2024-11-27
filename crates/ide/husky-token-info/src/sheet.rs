use crate::*;
use husky_entity_tree::region_path::SynNodeRegionPath;
use husky_regional_token::RegionalTokenIdx;
use husky_text_protocol::range::TextPositionRange;
use husky_token_data::TokenData;
use smallvec::{smallvec, SmallVec};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TokenInfoSheet {
    token_infos_list: Vec<TokenInfos>,
}

pub type TokenInfos = SmallVec<[TokenInfo; 2]>;

impl TokenInfoSheet {
    pub fn to_ref(&self) -> TokenInfoSheetRef {
        TokenInfoSheetRef {
            token_infos_list: &self.token_infos_list,
        }
    }
}

impl std::ops::Index<TokenIdx> for TokenInfoSheet {
    type Output = [TokenInfo];

    fn index(&self, idx: TokenIdx) -> &Self::Output {
        &self.token_infos_list[idx.index()]
    }
}

pub struct TokenInfoSheetRef<'a> {
    token_infos_list: &'a [TokenInfos],
}

impl<'a> std::ops::Index<TokenIdx> for TokenInfoSheetRef<'a> {
    type Output = [TokenInfo];

    fn index(&self, idx: TokenIdx) -> &Self::Output {
        &self.token_infos_list[idx.index()]
    }
}

impl TokenInfoSheet {
    pub(crate) fn new(token_sheet: &TokenSheetData) -> Self {
        TokenInfoSheet {
            token_infos_list: (0..token_sheet.len())
                .into_iter()
                .map(|_| smallvec![])
                .collect(),
        }
    }

    pub(crate) fn add(
        &mut self,
        token_idx: TokenIdx,
        regional_token_idx: impl Into<Option<RegionalTokenIdx>>,
        src: impl Into<TokenInfoSource>,
        token_info_data: TokenInfoData,
    ) {
        self.token_infos_list[token_idx.index()].push(TokenInfo::new(
            regional_token_idx.into(),
            src,
            token_info_data,
        ))
    }

    pub fn informative_ranged_token_iter<'db>(
        &'db self,
        ranged_token_sheet: &'db RangedTokenSheet,
        db: &'db ::salsa::Db,
    ) -> impl Iterator<Item = (&'db [TokenInfo], (&'db TextPositionRange, &'db TokenData))> + 'db
    {
        std::iter::zip(
            self.token_infos_list.iter(),
            ranged_token_sheet.ranged_token_iter(db),
        )
        .map(|(infos, other)| (infos.as_ref(), other))
    }
}
