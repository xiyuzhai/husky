use crate::{
    menu::{vd_ty_menu, VdTypeMenu},
    ty::VdType,
};
use rustc_hash::FxHashMap;
use visored_item_path::{
    menu::{vd_item_path_menu, VdItemPathMenu},
    path::VdItemPath,
};

pub struct VdItemPathZfcTypeTable {
    tys: FxHashMap<VdItemPath, VdType>,
}

impl VdItemPathZfcTypeTable {
    pub fn new(tys: impl IntoIterator<Item = (VdItemPath, VdType)>) -> Self {
        Self {
            tys: tys.into_iter().collect(),
        }
    }

    pub fn new_standard(db: &::salsa::Db) -> Self {
        // TODO: use menu?
        let VdItemPathMenu {
            nat: nat_path,
            int: int_path,
            rat: rat_path,
            real: real_path,
            complex: complex_path,
            set: set_path,
            prop: prop_path,
            sin: sin_path,
            cos: cos_path,
            group: group_path,
            ring: ring_path,
            group_mul: group_mul_path,
            abelian_group_add: abelian_group_add_path,
            ring_add: ring_add_path,
            ring_mul: ring_mul_path,
            ring_power: ring_power_path,
            ring_pos: ring_pos_path,
            ring_neg: ring_neg_path,
            field_div: field_div_path,
            eq: eq_path,
            ne: ne_path,
            lt: lt_path,
            gt: gt_path,
            le: le_path,
            ge: ge_path,
            real_sqrt: real_sqrt_path,
        } = *vd_item_path_menu(db);
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *vd_ty_menu(db);
        Self::new([
            (nat_path.into(), set),
            (rat_path.into(), set),
            (int_path.into(), set),
            (real_path.into(), set),
            (complex_path.into(), set),
        ])
    }
}

impl std::ops::Index<VdItemPath> for VdItemPathZfcTypeTable {
    type Output = VdType;
    fn index(&self, item_path: VdItemPath) -> &Self::Output {
        &self.tys[&item_path]
    }
}
