use super::*;
use crate::registry::assoc_trace::VoidAssocTraceRegistry;
use husky_entity_tree::node::HasSynNodePath;
use husky_syn_defn::item_syn_defn;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyCallTracePathData {
    biological_parent_path: TracePath,
    callee_path: ItemPath,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct LazyCallTraceData {
    path: TracePath,
    biological_parent: Trace,
    callee_path: ItemPath,
}

impl Trace {
    pub(crate) fn new_lazy_call(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        callee_path: ItemPath,
        db: &::salsa::Db,
    ) -> Self {
        let path = TracePath::new(
            LazyCallTracePathData {
                biological_parent_path: biological_parent_path.into(),
                callee_path,
            },
            db,
        );
        Trace::new(
            path,
            LazyCallTraceData {
                path,
                biological_parent: biological_parent.into(),
                callee_path,
            }
            .into(),
            db,
        )
    }
}

impl LazyCallTraceData {
    pub fn view_lines(&self, db: &::salsa::Db) -> TraceViewLines {
        let callee_path = self.callee_path;
        TraceViewLines::new(
            callee_path.module_path(db),
            callee_path
                .syn_node_path(db)
                .decl_tokra_region_token_idx_range(db),
            VoidAssocTraceRegistry,
            db,
        )
    }

    pub fn have_subtraces(&self, db: &::salsa::Db) -> bool {
        item_syn_defn(db, self.callee_path).is_some()
    }

    pub fn subtraces(&self, trace: Trace, db: &::salsa::Db) -> Vec<Trace> {
        Trace::new_lazy_stmts_from_syn_body_with_syn_expr_region(
            self.path,
            trace,
            item_syn_defn(db, self.callee_path),
            db,
        )
    }

    pub fn ki_repr(&self, db: &::salsa::Db) -> KiRepr {
        self.biological_parent.ki_repr(db).expect("should be some")
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        todo!()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        todo!()
    }

    pub(crate) fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
