use crate::static_mut_deps::SemStaticMutDeps;
use husky_sem_expr::SemExprMap;
use vec_like::OrderedSmallVecSet;

#[salsa::tracked]
pub struct SemStaticMutDepsRegion {
    #[return_ref]
    static_mut_deps_table: SemExprMap<SemStaticMutDeps>,
}