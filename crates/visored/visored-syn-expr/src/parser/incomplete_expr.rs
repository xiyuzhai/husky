mod call_list;
mod separated_list;

pub(super) use self::call_list::*;
pub(super) use self::separated_list::*;

use super::*;
use crate::expr::VdSynExprData;
use expr::{
    list_item::VdSynSeparatedListItem, VdSynBinaryOpr, VdSynExprArenaRef, VdSynLeftDelimiter,
    VdSynPrefixOpr, VdSynSeparator,
};
use latex_token::idx::LxTokenIdx;
use std::fmt::Formatter;
use visored_opr::{
    delimiter::VdBaseLeftDelimiter,
    opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr},
    precedence::VdPrecedence,
    separator::{VdBaseSeparator, VdSeparatorClass},
};

#[derive(Debug, PartialEq, Eq)]
pub(super) enum IncompleteVdSynExprData {
    Binary {
        lopd: VdSynExprIdx,
        opr: VdSynBinaryOpr,
    },
    Prefix {
        opr: VdSynPrefixOpr,
    },
    /// list separated by commas
    /// ```husky
    /// A(a, b, c)
    /// ```
    SeparatedList {
        separator_class: VdSeparatorClass,
        items: SmallVec<[VdSynExprData; 4]>,
        separators: SmallVec<[VdSynSeparator; 4]>,
    },
    Delimited {
        left_delimiter: VdSynLeftDelimiter,
    },
}

impl IncompleteVdSynExprData {
    pub(super) fn precedence(&self) -> VdPrecedence {
        match self {
            IncompleteVdSynExprData::Binary { opr, .. } => opr.precedence(),
            IncompleteVdSynExprData::Prefix { opr, .. } => opr.precedence(),
            IncompleteVdSynExprData::SeparatedList {
                separator_class, ..
            } => separator_class.precedence(),
            IncompleteVdSynExprData::Delimited { .. } => VdPrecedence::INCOMPLTE_DELIMITED,
        }
    }
}

impl IncompleteVdSynExprData {
    pub fn show(&self, arena: VdSynExprArenaRef) -> String {
        match *self {
            IncompleteVdSynExprData::Binary { lopd, opr } => {
                format!("{} {}", arena[lopd].show(arena), opr.show(arena))
            }
            IncompleteVdSynExprData::Prefix { opr } => opr.show(arena),
            IncompleteVdSynExprData::SeparatedList {
                separator_class,
                ref items,
                ref separators,
            } => {
                let mut s = String::new();

                // Interleave items and separators
                for (i, item) in items.iter().enumerate() {
                    if !s.is_empty() {
                        s += " ";
                    }
                    s += &item.show(arena);

                    // Add separator if there is one
                    if i < separators.len() {
                        s += " ";
                        s += &separators[i].show(arena);
                    }
                }
                s
            }
            IncompleteVdSynExprData::Delimited { left_delimiter } => {
                format!("{}", left_delimiter.show(arena))
            }
        }
    }
}
