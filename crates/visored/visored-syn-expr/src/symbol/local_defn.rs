pub mod letter;
pub mod punctuation;

use super::*;
use clause::VdSynClauseIdx;
use idx_arena::{Arena, ArenaIdx};
use latex_token::idx::LxTokenIdxRange;
use lineage::VdSynLineage;
use visored_item_path::module::VdModulePath;

/// Be careful with the wording.
///
/// "local" means the definition itself is local.
///
/// The symbol itself might not be local.
pub struct VdSynSymbolLocalDefnData {
    head: VdSynSymbolLocalDefnHead,
    body: VdSynSymbolLocalDefnBody,
    src: VdSynSymbolLocalDefnSrc,
    lineage: VdSynLineage,
    module_path: VdModulePath,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnHead {
    Letter {
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    },
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

pub type VdSynSymbolLocalDefnArena = Arena<VdSynSymbolLocalDefnData>;
pub type VdSynSymbolLocalDefnIdx = ArenaIdx<VdSynSymbolLocalDefnData>;

impl VdSynSymbolLocalDefnData {
    pub fn head(&self) -> &VdSynSymbolLocalDefnHead {
        &self.head
    }

    pub fn body(&self) -> &VdSynSymbolLocalDefnBody {
        &self.body
    }

    pub fn src(&self) -> VdSynSymbolLocalDefnSrc {
        self.src
    }

    pub fn module_path(&self) -> VdModulePath {
        self.module_path
    }
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

#[derive(Default)]
pub struct VdSynSymbolLocalDefnStorage {
    defn_arena: VdSynSymbolLocalDefnArena,
}

/// # getters
impl VdSynSymbolLocalDefnStorage {
    pub fn defn_arena(&self) -> &VdSynSymbolLocalDefnArena {
        &self.defn_arena
    }

    pub(crate) fn resolve_letter<'a>(
        &'a self,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> impl Iterator<Item = VdSynSymbolLocalDefnIdx> + 'a {
        // TODO: take scope into account
        self.defn_arena
            .indexed_iter()
            .filter_map(move |(idx, defn)| defn.head.is_letter(letter).then_some(idx))
    }
}

/// # actions
impl VdSynSymbolLocalDefnStorage {
    pub(crate) fn define_symbol(
        &mut self,
        head: VdSynSymbolLocalDefnHead,
        body: VdSynSymbolLocalDefnBody,
        src: VdSynSymbolLocalDefnSrc,
        lineage: VdSynLineage,
        module_path: VdModulePath,
    ) {
        self.defn_arena.alloc_one(VdSynSymbolLocalDefnData {
            head,
            body,
            src,
            lineage,
            module_path,
        });
    }
}
