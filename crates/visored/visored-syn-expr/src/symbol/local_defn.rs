pub mod letter;
pub mod punctuation;

use super::*;
use clause::VdSynClauseIdx;
use idx_arena::{Arena, ArenaIdx};
use latex_token::idx::LxTokenIdxRange;

/// Be careful with the wording.
///
/// "local" means the definition itself is local.
///
/// The symbol itself might not be local.
pub struct VdSynSymbolLocalDefn {
    head: VdSynSymbolLocalDefnHead,
    body: VdSynSymbolLocalDefnBody,
    src: VdSynSymbolLocalDefnSrc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnHead {
    Letter {
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    },
}
impl VdSynSymbolLocalDefnHead {
    fn is_letter(&self, letter: LxMathLetter) -> bool {
        match *self {
            VdSynSymbolLocalDefnHead::Letter {
                letter: letter1, ..
            } => letter == letter1,
        }
    }
}

pub enum VdSynSymbolLocalDefnBody {
    Placeholder,
    Assigned,
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnSrc {
    Clause(VdSynClauseIdx),
    Expr(VdSynExprIdx),
}

pub type VdSynSymbolLocalDefnArena = Arena<VdSynSymbolLocalDefn>;
pub type VdSynSymbolLocalDefnIdx = ArenaIdx<VdSynSymbolLocalDefn>;

#[derive(Default)]
pub struct VdSynSymbolLocalDefnTable {
    defns: VdSynSymbolLocalDefnArena,
}

/// # getters
impl VdSynSymbolLocalDefnTable {
    pub fn defns(&self) -> &VdSynSymbolLocalDefnArena {
        &self.defns
    }

    pub(crate) fn resolve_letter<'a>(
        &'a self,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> impl Iterator<Item = VdSynSymbolLocalDefnIdx> + 'a {
        // TODO: take scope into account
        self.defns
            .indexed_iter()
            .filter_map(move |(idx, defn)| defn.head.is_letter(letter).then_some(idx))
    }
}

/// # actions
impl VdSynSymbolLocalDefnTable {
    pub(crate) fn define_symbol(
        &mut self,
        head: VdSynSymbolLocalDefnHead,
        body: VdSynSymbolLocalDefnBody,
        src: VdSynSymbolLocalDefnSrc,
    ) {
        self.defns
            .alloc_one(VdSynSymbolLocalDefn { head, body, src });
    }
}
