mod fugitive;
mod trai;
mod ty;

pub use self::fugitive::*;
pub use self::trai::*;
pub use self::ty::*;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db(db = SynDefnDb)]
#[enum_class::from_variants]
pub enum ModuleItemSynNodeDefn {
    Type(TypeSynNodeDefn),
    Trait(TraitSynNodeDefn),
    Fugitive(FugitiveSynNodeDefn),
}

impl ModuleItemSynNodeDefn {
    pub fn node_decl(self, db: &dyn SynDefnDb) -> ModuleItemSynNodeDecl {
        match self {
            ModuleItemSynNodeDefn::Type(node_defn) => node_defn.node_decl(db).into(),
            ModuleItemSynNodeDefn::Trait(node_defn) => node_defn.node_decl(db).into(),
            ModuleItemSynNodeDefn::Fugitive(node_defn) => node_defn.node_decl(db).into(),
        }
    }

    pub fn expr_region(self, db: &dyn SynDefnDb) -> Option<SynExprRegion> {
        match self {
            ModuleItemSynNodeDefn::Type(_) | ModuleItemSynNodeDefn::Trait(_) => None,
            ModuleItemSynNodeDefn::Fugitive(node_defn) => Some(node_defn.expr_region(db)),
        }
    }
}

impl HasSynNodeDefn for ModuleItemSynNodePath {
    type NodeDefn = ModuleItemSynNodeDefn;

    fn node_defn(self, db: &dyn SynDefnDb) -> Self::NodeDefn {
        match self {
            ModuleItemSynNodePath::Trait(node_path) => node_path.node_defn(db).into(),
            ModuleItemSynNodePath::Type(node_path) => node_path.node_defn(db).into(),
            ModuleItemSynNodePath::Fugitive(node_path) => node_path.node_defn(db).into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db(db = SynDefnDb)]
#[enum_class::from_variants]
pub enum ModuleItemDefn {
    Type(TypeDefn),
    Trait(TraitDefn),
    Fugitive(FugitiveDefn),
}

impl ModuleItemDefn {
    pub fn decl(self, db: &dyn SynDefnDb) -> ModuleItemDecl {
        match self {
            ModuleItemDefn::Type(defn) => defn.decl(db).into(),
            ModuleItemDefn::Trait(defn) => defn.decl(db).into(),
            ModuleItemDefn::Fugitive(defn) => defn.decl(db).into(),
        }
    }

    pub fn expr_region(self, db: &dyn SynDefnDb) -> Option<SynExprRegion> {
        match self {
            ModuleItemDefn::Type(_) | ModuleItemDefn::Trait(_) => None,
            ModuleItemDefn::Fugitive(defn) => Some(defn.expr_region(db)),
        }
    }
}

impl HasDefn for ModuleItemPath {
    type Defn = ModuleItemDefn;

    fn defn(self, db: &dyn SynDefnDb) -> DefnResult<Self::Defn> {
        Ok(match self {
            ModuleItemPath::Type(path) => path.defn(db)?.into(),
            ModuleItemPath::Fugitive(path) => path.defn(db)?.into(),
            ModuleItemPath::Trait(path) => path.defn(db)?.into(),
        })
    }
}