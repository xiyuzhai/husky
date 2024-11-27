use crate::{
    menu::{VdTypeMenu, VD_TYPE_MENU},
    ty::VdType,
};
use rustc_hash::FxHashMap;
use visored_entity_path::{
    menu::{VdItemPathMenu, VD_ITEM_PATH_MENU},
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

    pub fn new_standard() -> Self {
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
            nat_add: nat_add_path,
            nat_mul: nat_mul_path,
            ring_add: ring_add_path,
            ring_sub: ring_sub_path,
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
        } = *VD_ITEM_PATH_MENU;
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *VD_TYPE_MENU;
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
