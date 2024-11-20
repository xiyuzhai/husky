use crate::*;
use lean_coword::ident::LnIdent;
use rustc_hash::FxHashMap;
use visored_mir_expr::symbol::local_defn::{
    storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
    VdMirSymbolLocalDefnOrderedMap,
};

pub struct VdLeanTranspilationMangler {
    local_defn_mangled_symbols: VdMirSymbolLocalDefnOrderedMap<LnIdent>,
    ident_to_source_map: FxHashMap<LnIdent, VdLeanMangleSrc>,
    disambiguator_map: FxHashMap<String, usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdLeanMangleSrc {
    SymbolLocalDefn(VdMirSymbolLocalDefnIdx),
}

impl VdLeanTranspilationMangler {
    pub(crate) fn new(storage: &VdMirSymbolLocalDefnStorage, db: &::salsa::Db) -> Self {
        let mut local_defn_mangled_symbols: VdMirSymbolLocalDefnOrderedMap<LnIdent> =
            Default::default();
        let mut ident_to_source_map: FxHashMap<LnIdent, VdLeanMangleSrc> = FxHashMap::default();
        let mut disambiguator_map: FxHashMap<String, usize> = FxHashMap::default();
        for (idx, defn) in storage.defn_arena().indexed_iter() {
            let naive_ident = naive_ident(defn.head());
            let mangled_ident = mangle_naive_ident(naive_ident, &mut disambiguator_map, db);
            local_defn_mangled_symbols.insert_next(idx, mangled_ident);
            ident_to_source_map.insert(mangled_ident, VdLeanMangleSrc::SymbolLocalDefn(idx));
        }
        Self {
            local_defn_mangled_symbols,
            ident_to_source_map,
            disambiguator_map,
        }
    }

    pub(crate) fn mangle_symbol(&self, symbol_local_defn: VdMirSymbolLocalDefnIdx) -> LnIdent {
        self.local_defn_mangled_symbols[symbol_local_defn]
    }

    pub(crate) fn mangle_hypothesis(&mut self, db: &::salsa::Db) -> LnIdent {
        match self.disambiguator_map.get_mut("h") {
            Some(count) => {
                *count += 1;
                LnIdent::from_ref(&format!("h{}", count), db)
            }
            None => {
                self.disambiguator_map.insert("h".to_string(), 0);
                LnIdent::from_ref("h", db)
            }
        }
    }
}

fn naive_ident(head: &VdMirSymbolLocalDefnHead) -> String {
    match *head {
        VdMirSymbolLocalDefnHead::Letter(letter) => letter.to_string(),
    }
}

fn mangle_naive_ident(
    naive_ident: String,
    disambiguator_map: &mut FxHashMap<String, usize>,
    db: &::salsa::Db,
) -> LnIdent {
    // If the identifier hasn't been used before, use it as-is
    let mangled = if !disambiguator_map.contains_key(&naive_ident) {
        disambiguator_map.insert(naive_ident.clone(), 0);
        naive_ident
    } else {
        // Get the next number in sequence and increment it
        let next_num = disambiguator_map.get(&naive_ident).unwrap() + 1;
        disambiguator_map.insert(naive_ident.clone(), next_num);
        format!("{}{}", naive_ident, next_num)
    };

    LnIdent::from_owned(mangled, db)
}

#[test]
fn test_mangle_naive_ident() {
    use expect_test::expect;
    let mut disambiguator_map = FxHashMap::default();
    let db = &DB::default(); // Assuming you have a test database setup

    // First occurrence should be unchanged
    let result1 = mangle_naive_ident("x".to_string(), &mut disambiguator_map, db);
    expect!["x"].assert_eq(&result1.data(db));

    // Second occurrence should be x1
    let result2 = mangle_naive_ident("x".to_string(), &mut disambiguator_map, db);
    expect!["x1"].assert_eq(&result2.data(db));

    // Third occurrence should be x2
    let result3 = mangle_naive_ident("x".to_string(), &mut disambiguator_map, db);
    expect!["x2"].assert_eq(&result3.data(db));

    // Different letter should start fresh
    let result4 = mangle_naive_ident("y".to_string(), &mut disambiguator_map, db);
    expect!["y"].assert_eq(&result4.data(db));

    // Second occurrence of y should be y1
    let result5 = mangle_naive_ident("y".to_string(), &mut disambiguator_map, db);
    expect!["y1"].assert_eq(&result5.data(db));
}
