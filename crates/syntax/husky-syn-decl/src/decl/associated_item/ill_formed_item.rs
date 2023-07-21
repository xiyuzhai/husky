use super::*;

#[salsa::tracked(db = DeclDb, jar = SynDeclJar)]
pub struct IllFormedItemNodeDecl {
    #[id]
    pub node_path: IllFormedItemSynNodePath,
    pub node: IllFormedItemNode,
}

impl From<IllFormedItemNodeDecl> for SynNodeDecl {
    fn from(decl: IllFormedItemNodeDecl) -> Self {
        SynNodeDecl::AssociatedItem(decl.into())
    }
}

impl HasNodeDecl for IllFormedItemSynNodePath {
    type NodeDecl = IllFormedItemNodeDecl;

    fn node_decl<'a>(self, db: &'a dyn DeclDb) -> Self::NodeDecl {
        todo!()
    }
}