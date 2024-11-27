use super::*;
use husky_entity_path::path::submodule::SubmoduleItemPath;
use husky_entity_tree::node::submodule::SubmoduleSynNodePath;

#[salsa::tracked]
pub struct SubmoduleSynNodeDecl {
    #[id]
    pub syn_node_path: SubmoduleSynNodePath,
}

impl SubmoduleSynNodeDecl {
    pub fn errors(self, _db: &::salsa::Db) -> SynNodeDeclErrorRefs {
        Default::default()
    }
}

impl HasSynNodeDecl for SubmoduleSynNodePath {
    type NodeDecl = SubmoduleSynNodeDecl;

    fn syn_node_decl<'a>(self, db: &'a ::salsa::Db) -> Self::NodeDecl {
        submodule_syn_node_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn submodule_syn_node_decl(
    db: &::salsa::Db,
    syn_node_path: SubmoduleSynNodePath,
) -> SubmoduleSynNodeDecl {
    SubmoduleSynNodeDecl::new(db, syn_node_path)
}

#[salsa::tracked(db = SynDeclDb, jar = SynDeclJar, constructor = new)]
pub struct SubmoduleSynDecl {
    #[id]
    pub path: SubmoduleItemPath,
}

impl SubmoduleSynDecl {
    #[inline(always)]
    fn from_node(
        db: &::salsa::Db,
        path: SubmoduleItemPath,
        _syn_node_decl: SubmoduleSynNodeDecl,
    ) -> Self {
        Self::new(db, path)
    }
}

// actually it only works for nonroot module path
// but rust doesn't provide refinement type
impl HasSynDecl for SubmoduleItemPath {
    type Decl = SubmoduleSynDecl;

    fn syn_decl(self, db: &::salsa::Db) -> SynDeclResult<Self::Decl> {
        submodule_decl(db, self)
    }
}

#[salsa::tracked(jar = SynDeclJar)]
pub(crate) fn submodule_decl(
    db: &::salsa::Db,
    path: SubmoduleItemPath,
) -> SynDeclResult<SubmoduleSynDecl> {
    let syn_node_path = path.syn_node_path(db);
    let syn_node_decl = syn_node_path.syn_node_decl(db);
    Ok(SubmoduleSynDecl::from_node(db, path, syn_node_decl))
}
