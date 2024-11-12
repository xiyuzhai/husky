pub mod defn;
pub mod resolution;

use crate::{
    ast::{Ast, AstData},
    token::{
        ident::Ident,
        keyword::{DefnKeyword, Keyword},
    },
    *,
};
use ast::calc_asts_from_input;
use cybertron::{prelude::Idx, seq::Seq};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Symbol {
    ident: Ident,
    source: Idx,
    data: SymbolData,
}

impl Symbol {
    pub fn ident(&self) -> Ident {
        self.ident
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolData {
    Item { kind: ItemKind },
    Variable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Struct,
    Enum,
    Fn,
}

impl From<DefnKeyword> for ItemKind {
    fn from(kw: DefnKeyword) -> Self {
        match kw {
            DefnKeyword::Struct => ItemKind::Struct,
            DefnKeyword::Enum => ItemKind::Enum,
            DefnKeyword::Fn => ItemKind::Fn,
        }
    }
}
