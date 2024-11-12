use super::*;
use husky_entity_path::path::ItemPath;
use husky_sem_expr::{helpers::path::sem_expr_region_from_region_path, SemExprRegion};
use husky_syn_defn::item_syn_defn;
use husky_syn_defn::ItemSynDefn;

pub fn hir_eager_body_with_expr_region(
    item_path: ItemPath,
    db: &::salsa::Db,
) -> Option<(HirEagerExprIdx, HirEagerExprRegion)> {
    let ItemSynDefn {
        body,
        syn_expr_region,
    } = item_syn_defn(db, item_path)?;
    let sem_expr_region = db.sem_expr_region(syn_expr_region);
    let (hir_eager_expr_region, hir_eager_source_map) =
        hir_eager_expr_region_with_source_map(db, sem_expr_region);
    let hir_eager_source_map_data = hir_eager_source_map.data(db);
    let body = sem_expr_region.data(db).syn_root_to_sem_expr_idx(body);
    let Some(body) = hir_eager_source_map_data.sem_to_hir_eager_expr_idx(body) else {
        todo!()
    };
    Some((body, hir_eager_expr_region))
}

pub fn hir_eager_expr_region(
    syn_expr_region: SynExprRegion,
    db: &::salsa::Db,
) -> HirEagerExprRegion {
    let sem_expr_region = db.sem_expr_region(syn_expr_region);
    hir_eager_expr_region_with_source_map(db, sem_expr_region).0
}

pub fn hir_eager_expr_source_map_from_sem(
    sem_expr_region: SemExprRegion,
    db: &::salsa::Db,
) -> HirEagerExprSourceMap {
    hir_eager_expr_region_with_source_map(db, sem_expr_region).1
}

impl HirEagerExprRegion {
    pub fn sem_expr_region(self, db: &::salsa::Db) -> SemExprRegion {
        let region_path = self.region_path(db);
        sem_expr_region_from_region_path(region_path, db).unwrap()
    }
}
