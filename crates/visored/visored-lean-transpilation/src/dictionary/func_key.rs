use lean_mir_expr::expr::application::{ln_mir_func_key_menu, LnMirFuncKey, LnMirFuncKeyMenu};
use rustc_hash::FxHashMap;
use visored_mir_expr::expr::application::{
    menu::{vd_mir_func_key_menu, VdMirFuncKeyMenu},
    VdMirFunc, VdMirFuncKey,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdFuncKeyTranslation {
    PrefixOpr(LnMirFuncKey),
    FoldingBinaryOpr(LnMirFuncKey),
    ChainingBinaryOpr(LnMirFuncKey),
    Power(LnMirFuncKey),
    Function(LnMirFuncKey),
    JustBinaryOpr(LnMirFuncKey),
    InSet,
}

#[derive(Debug, PartialEq, Eq)]
pub struct VdFuncKeyDictionary {
    translations: FxHashMap<VdMirFuncKey, VdFuncKeyTranslation>,
}

impl VdFuncKeyDictionary {
    pub fn new_standard() -> Self {
        use VdFuncKeyTranslation::*;

        let VdMirFuncKeyMenu {
            int_pos,
            rat_pos,
            real_pos,
            complex_pos,
            int_neg,
            rat_neg,
            real_neg,
            complex_neg,
            int_sub,
            rat_sub,
            real_sub,
            complex_sub,
            rat_div,
            real_div,
            complex_div,
            nat_add,
            int_add,
            rat_add,
            real_add,
            complex_add,
            nat_mul,
            int_mul,
            rat_mul,
            real_mul,
            complex_mul,
            nat_to_the_power_of_nat,
            int_to_the_power_of_nat,
            rat_to_the_power_of_nat,
            real_to_the_power_of_nat,
            complex_to_the_power_of_nat,
            nat_eq,
            int_eq,
            rat_eq,
            real_eq,
            complex_eq,
            nat_ne,
            int_ne,
            rat_ne,
            real_ne,
            complex_ne,
            nat_lt,
            int_lt,
            rat_lt,
            real_lt,
            nat_gt,
            int_gt,
            rat_gt,
            real_gt,
            nat_le,
            int_le,
            rat_le,
            real_le,
            nat_ge,
            int_ge,
            rat_ge,
            real_ge,
            in_set,
            real_sqrt,
            rat_frac,
            real_frac,
            complex_frac,
        } = *vd_mir_func_key_menu;
        let LnMirFuncKeyMenu {
            int_pos: ln_int_pos,
            rat_pos: ln_rat_pos,
            real_pos: ln_real_pos,
            complex_pos: ln_complex_pos,
            int_neg: ln_int_neg,
            rat_neg: ln_rat_neg,
            real_neg: ln_real_neg,
            complex_neg: ln_complex_neg,
            int_sub: ln_int_sub,
            rat_sub: ln_rat_sub,
            real_sub: ln_real_sub,
            complex_sub: ln_complex_sub,
            rat_div: ln_rat_div,
            real_div: ln_real_div,
            complex_div: ln_complex_div,
            nat_add: ln_nat_add,
            int_add: ln_int_add,
            rat_add: ln_rat_add,
            real_add: ln_real_add,
            complex_add: ln_complex_add,
            nat_mul: ln_nat_mul,
            int_mul: ln_int_mul,
            rat_mul: ln_rat_mul,
            real_mul: ln_real_mul,
            complex_mul: ln_complex_mul,
            nat_to_the_power_of_nat: ln_nat_to_the_power_of_nat,
            int_to_the_power_of_nat: ln_int_to_the_power_of_nat,
            rat_to_the_power_of_nat: ln_rat_to_the_power_of_nat,
            real_to_the_power_of_nat: ln_real_to_the_power_of_nat,
            complex_to_the_power_of_nat: ln_complex_to_the_power_of_nat,
            nat_eq: ln_nat_eq,
            int_eq: ln_int_eq,
            rat_eq: ln_rat_eq,
            real_eq: ln_real_eq,
            complex_eq: ln_complex_eq,
            nat_ne: ln_nat_ne,
            int_ne: ln_int_ne,
            rat_ne: ln_rat_ne,
            real_ne: ln_real_ne,
            complex_ne: ln_complex_ne,
            nat_lt: ln_nat_lt,
            int_lt: ln_int_lt,
            rat_lt: ln_rat_lt,
            real_lt: ln_real_lt,
            nat_gt: ln_nat_gt,
            int_gt: ln_int_gt,
            rat_gt: ln_rat_gt,
            real_gt: ln_real_gt,
            nat_le: ln_nat_le,
            int_le: ln_int_le,
            rat_le: ln_rat_le,
            real_le: ln_real_le,
            nat_ge: ln_nat_ge,
            int_ge: ln_int_ge,
            rat_ge: ln_rat_ge,
            real_ge: ln_real_ge,
            real_sqrt: ln_real_sqrt,
        } = *ln_mir_func_key_menu;
        Self::new([
            (int_pos, PrefixOpr(ln_int_pos)),
            (rat_pos, PrefixOpr(ln_rat_pos)),
            (real_pos, PrefixOpr(ln_real_pos)),
            (complex_pos, PrefixOpr(ln_complex_pos)),
            (int_neg, PrefixOpr(ln_int_neg)),
            (rat_neg, PrefixOpr(ln_rat_neg)),
            (real_neg, PrefixOpr(ln_real_neg)),
            (complex_neg, FoldingBinaryOpr(ln_complex_neg)),
            (int_sub, JustBinaryOpr(ln_int_sub)),
            (rat_sub, JustBinaryOpr(ln_rat_sub)),
            (real_sub, JustBinaryOpr(ln_real_sub)),
            (complex_sub, JustBinaryOpr(ln_complex_sub)),
            (rat_div, JustBinaryOpr(ln_rat_div)),
            (real_div, JustBinaryOpr(ln_real_div)),
            (complex_div, JustBinaryOpr(ln_complex_div)),
            (nat_add, FoldingBinaryOpr(ln_nat_add)),
            (int_add, FoldingBinaryOpr(ln_int_add)),
            (rat_add, FoldingBinaryOpr(ln_rat_add)),
            (real_add, FoldingBinaryOpr(ln_real_add)),
            (complex_add, FoldingBinaryOpr(ln_complex_add)),
            (nat_mul, FoldingBinaryOpr(ln_nat_mul)),
            (int_mul, FoldingBinaryOpr(ln_int_mul)),
            (rat_mul, FoldingBinaryOpr(ln_rat_mul)),
            (real_mul, FoldingBinaryOpr(ln_real_mul)),
            (complex_mul, FoldingBinaryOpr(ln_complex_mul)),
            (nat_to_the_power_of_nat, Power(ln_nat_to_the_power_of_nat)),
            (int_to_the_power_of_nat, Power(ln_int_to_the_power_of_nat)),
            (rat_to_the_power_of_nat, Power(ln_rat_to_the_power_of_nat)),
            (real_to_the_power_of_nat, Power(ln_real_to_the_power_of_nat)),
            (
                complex_to_the_power_of_nat,
                Power(ln_complex_to_the_power_of_nat),
            ),
            (nat_eq, ChainingBinaryOpr(ln_nat_eq)),
            (int_eq, ChainingBinaryOpr(ln_int_eq)),
            (rat_eq, ChainingBinaryOpr(ln_rat_eq)),
            (real_eq, ChainingBinaryOpr(ln_real_eq)),
            (complex_eq, ChainingBinaryOpr(ln_complex_eq)),
            (nat_ne, ChainingBinaryOpr(ln_nat_ne)),
            (int_ne, ChainingBinaryOpr(ln_int_ne)),
            (rat_ne, ChainingBinaryOpr(ln_rat_ne)),
            (real_ne, ChainingBinaryOpr(ln_real_ne)),
            (nat_lt, ChainingBinaryOpr(ln_nat_lt)),
            (int_lt, ChainingBinaryOpr(ln_int_lt)),
            (rat_lt, ChainingBinaryOpr(ln_rat_lt)),
            (real_lt, ChainingBinaryOpr(ln_real_lt)),
            (nat_gt, ChainingBinaryOpr(ln_nat_gt)),
            (int_gt, ChainingBinaryOpr(ln_int_gt)),
            (rat_gt, ChainingBinaryOpr(ln_rat_gt)),
            (real_gt, ChainingBinaryOpr(ln_real_gt)),
            (nat_le, ChainingBinaryOpr(ln_nat_le)),
            (int_le, ChainingBinaryOpr(ln_int_le)),
            (rat_le, ChainingBinaryOpr(ln_rat_le)),
            (real_le, ChainingBinaryOpr(ln_real_le)),
            (nat_ge, ChainingBinaryOpr(ln_nat_ge)),
            (int_ge, ChainingBinaryOpr(ln_int_ge)),
            (rat_ge, ChainingBinaryOpr(ln_rat_ge)),
            (real_ge, ChainingBinaryOpr(ln_real_ge)),
            (in_set, InSet),
            (real_sqrt, Function(ln_real_sqrt)),
            (rat_frac, JustBinaryOpr(ln_rat_div)),
            (real_frac, JustBinaryOpr(ln_real_div)),
            (complex_frac, JustBinaryOpr(ln_complex_div)),
        ])
    }

    pub fn new(
        translations: impl IntoIterator<Item = (VdMirFuncKey, VdFuncKeyTranslation)> + Clone,
    ) -> Self {
        #[cfg(debug_assertions)]
        {
            let translations_vec: Vec<_> = translations.clone().into_iter().collect();
            let mut seen = std::collections::HashMap::new();
            for (idx, (key, _)) in translations_vec.iter().enumerate() {
                if let Some(prev_idx) = seen.insert(key, idx) {
                    panic!(
                        "Duplicate key {:?} found at positions {} and {}",
                        key, prev_idx, idx
                    );
                }
            }
        }
        Self {
            translations: translations.into_iter().collect(),
        }
    }
}

impl VdFuncKeyDictionary {
    pub fn get(&self, func_key: VdMirFuncKey) -> Option<&VdFuncKeyTranslation> {
        self.translations.get(&func_key)
    }
}
