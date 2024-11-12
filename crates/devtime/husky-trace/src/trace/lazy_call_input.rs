use husky_hir_lazy_expr::HirLazyExprIdx;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct LazyCallInputTracePathData {
    biological_parent_path: TracePath,
    // todo: add more?
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LazyCallInputTraceData {
    path: TracePath,
    biological_parent: Trace,
    input_sketch: LazyCallInputSketch,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum LazyCallInputSketch {
    Simple {
        sem_expr_idx: SemExprIdx,
        hir_lazy_expr_idx: Option<HirLazyExprIdx>,
    },
    Variadic,
    Keyed,
}

impl Trace {
    pub(crate) fn new_lazy_call_input(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        input_sketch: LazyCallInputSketch,
        db: &::salsa::Db,
    ) -> Self {
        let path = TracePath::new(
            LazyCallInputTracePathData {
                biological_parent_path: biological_parent_path.into(),
            },
            db,
        );
        Trace::new(
            path,
            LazyCallInputTraceData {
                path,
                biological_parent: biological_parent.into(),
                input_sketch,
            }
            .into(),
            db,
        )
    }
}

impl LazyCallInputTraceData {
    pub fn view_lines(&self, _db: &::salsa::Db) -> TraceViewLines {
        todo!()
    }

    pub fn have_subtraces(&self) -> bool {
        false
    }

    pub fn subtraces(&self) -> Vec<Trace> {
        vec![]
    }

    pub fn ki_repr(&self, _db: &::salsa::Db) -> KiRepr {
        todo!()
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
