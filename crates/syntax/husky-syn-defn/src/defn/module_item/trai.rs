use super::*;

#[salsa::tracked(db = SynDefnDb, jar = SynDefnJar)]
pub struct TraitSynNodeDefn {
    #[id]
    pub node_path: TraitSynNodePath,
    pub node_decl: TraitNodeDecl,
}

impl HasSynNodeDefn for TraitSynNodePath {
    type NodeDefn = TraitSynNodeDefn;

    fn node_defn(self, db: &dyn SynDefnDb) -> Self::NodeDefn {
        trai_node_defn(db, self)
    }
}

#[salsa::tracked(jar = SynDefnJar)]
pub(crate) fn trai_node_defn(db: &dyn SynDefnDb, node_path: TraitSynNodePath) -> TraitSynNodeDefn {
    let node_decl = node_path.node_decl(db);
    TraitSynNodeDefn::new(db, node_path, node_decl)
}

#[salsa::tracked(db = SynDefnDb, jar = SynDefnJar)]
pub struct TraitDefn {
    #[id]
    pub path: TraitPath,
    pub decl: TraitDecl,
}

impl HasDefn for TraitPath {
    type Defn = TraitDefn;

    fn defn(self, db: &dyn SynDefnDb) -> DefnResult<Self::Defn> {
        trai_defn(db, self)
    }
}

#[salsa::tracked(jar = SynDefnJar)]
pub(crate) fn trai_defn(db: &dyn SynDefnDb, path: TraitPath) -> DefnResult<TraitDefn> {
    let decl = path.decl(db)?;
    Ok(TraitDefn::new(db, path, decl))
}