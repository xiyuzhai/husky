pub mod letter;
pub mod punctuation;

use super::*;
use clause::VdSynClauseIdx;
use idx_arena::{Arena, ArenaIdx};
use latex_token::idx::LxTokenIdxRange;
use lineage::VdSynLineage;
use visored_entity_path::module::VdModulePath;

/// Be careful with the wording.
///
/// "local" means the definition itself is local.
///
/// The symbol itself might not be local.
#[derive(Debug, PartialEq, Eq)]
pub struct VdSynSymbolLocalDefnData {
    head: VdSynSymbolLocalDefnHead,
    body: VdSynSymbolLocalDefnBody,
    src: VdSynSymbolLocalDefnSrc,
    lineage: VdSynLineage,
    module_path: VdModulePath,
    scope: VdSynSymbolLocalDefnScope,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnScope {
    Module(VdModulePath),
    /// Applies to symbols defined in the environments like theorems followed by a proof.
    ///
    /// Then the modules will be the theorem environment and the proof environment.
    Modules(SmallVec<[VdModulePath; 2]>),
}
impl VdSynSymbolLocalDefnScope {
    fn contains(&self, other_module_path: VdModulePath, token_idx_range: LxTokenIdxRange) -> bool {
        match *self {
            VdSynSymbolLocalDefnScope::Module(slf_module_path) => {
                slf_module_path.contains(other_module_path)
            }
            VdSynSymbolLocalDefnScope::Modules(ref module_paths) => todo!(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnHead {
    Letter {
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnBody {
    Placeholder,
    Assigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolLocalDefnSrc {
    LetAssigned(VdSynClauseIdx),
    LetPlaceholder(VdSynClauseIdx),
    // Expr(VdSynExprIdx),
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

impl std::fmt::Debug for VdSynSymbolLocalDefnStorage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
        // f.debug_struct("VdSynSymbolLocalDefnStorage").finish()
    }
}

/// # getters
impl VdSynSymbolLocalDefnStorage {
    pub fn defn_arena(&self) -> &VdSynSymbolLocalDefnArena {
        &self.defn_arena
    }

    pub(crate) fn resolve_letter<'a>(
        &'a self,
        module_path: VdModulePath,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> impl Iterator<Item = VdSynSymbolLocalDefnIdx> + 'a {
        // TODO: take scope into account
        // already used module_path, but this will not be enough.
        self.defn_arena
            .indexed_iter()
            .filter_map(move |(idx, defn)| {
                (defn.head.is_letter(letter) && defn.scope.contains(module_path, token_idx_range))
                    .then_some(idx)
            })
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
        scope: VdSynSymbolLocalDefnScope,
    ) {
        self.defn_arena.alloc_one(VdSynSymbolLocalDefnData {
            head,
            body,
            src,
            lineage,
            module_path,
            scope,
        });
    }
}
