use crate::*;
use eterned::db::EternerDb;
use lean_coword::ident::LnIdent;
use lean_entity_path::namespace::LnNamespace;
use namespace::vd_module_path_to_ln_namespace_or_inherited;
use rustc_hash::FxHashMap;
use visored_mir_expr::{
    derivation::{VdMirDerivationArenaRef, VdMirDerivationIdx, VdMirDerivationMap},
    hypothesis::{VdMirHypothesisArenaRef, VdMirHypothesisIdx, VdMirHypothesisMap},
    symbol::local_defn::{
        storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
        VdMirSymbolLocalDefnOrderedMap,
    },
};

type DisambiguatorMap = FxHashMap<(LnNamespace, String), usize>;

pub struct VdLeanTranspilationMangler {
    local_defn_mangled_symbols: VdMirSymbolLocalDefnOrderedMap<LnIdent>,
    hypothesis_mangled_symbols: VdMirHypothesisMap<LnIdent>,
    derivation_mangled_symbols: VdMirDerivationMap<LnIdent>,
    ident_to_source_map: FxHashMap<(LnNamespace, LnIdent), VdLeanMangleSrc>,
    disambiguator_map: DisambiguatorMap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdLeanMangleSrc {
    SymbolLocalDefn(VdMirSymbolLocalDefnIdx),
}

impl VdLeanTranspilationMangler {
    pub(crate) fn new(
        hypothesis_arena: VdMirHypothesisArenaRef,
        derivation_arena: VdMirDerivationArenaRef,
        storage: &VdMirSymbolLocalDefnStorage,
        db: &EternerDb,
    ) -> Self {
        let mut local_defn_mangled_symbols: VdMirSymbolLocalDefnOrderedMap<LnIdent> =
            Default::default();
        let mut ident_to_source_map: FxHashMap<(LnNamespace, LnIdent), VdLeanMangleSrc> =
            FxHashMap::default();
        let mut disambiguator_map: FxHashMap<(LnNamespace, String), usize> = FxHashMap::default();
        for (idx, defn) in storage.defn_arena().indexed_iter() {
            let namespace = vd_module_path_to_ln_namespace_or_inherited(defn.module_path(), db);
            let naive_ident = naive_ident(defn.head());
            let mangled_ident =
                mangle_naive_ident(namespace, naive_ident, &mut disambiguator_map, db);
            local_defn_mangled_symbols.insert_next(idx, mangled_ident);
            ident_to_source_map.insert(
                (namespace, mangled_ident),
                VdLeanMangleSrc::SymbolLocalDefn(idx),
            );
        }
        Self {
            local_defn_mangled_symbols,
            hypothesis_mangled_symbols: VdMirHypothesisMap::new2(hypothesis_arena),
            derivation_mangled_symbols: VdMirDerivationMap::new2(derivation_arena),
            ident_to_source_map,
            disambiguator_map,
        }
    }

    pub(crate) fn mangle_symbol(&self, symbol_local_defn: VdMirSymbolLocalDefnIdx) -> LnIdent {
        self.local_defn_mangled_symbols[symbol_local_defn]
    }

    pub(crate) fn mangle_hypothesis(
        &mut self,
        hypothesis: VdMirHypothesisIdx,
        namespace: LnNamespace,
        db: &EternerDb,
    ) -> LnIdent {
        *self
            .hypothesis_mangled_symbols
            .get_or_insert_with(hypothesis, || {
                new_hypothesis_ident(&mut self.disambiguator_map, namespace, db)
            })
    }

    pub(crate) fn new_hypothesis_ident(
        &mut self,
        namespace: LnNamespace,
        db: &EternerDb,
    ) -> LnIdent {
        new_hypothesis_ident(&mut self.disambiguator_map, namespace, db)
    }

    pub(crate) fn mangle_derivation(
        &mut self,
        derivation: VdMirDerivationIdx,
        namespace: LnNamespace,
        db: &EternerDb,
    ) -> LnIdent {
        *self
            .derivation_mangled_symbols
            .get_or_insert_with(derivation, || {
                new_derivation_ident(&mut self.disambiguator_map, namespace, db)
            })
    }
}

fn new_hypothesis_ident(
    disambiguator_map: &mut DisambiguatorMap,
    namespace: LnNamespace,
    db: &EternerDb,
) -> LnIdent {
    match disambiguator_map.get_mut(&(namespace, "h".to_string())) {
        Some(count) => {
            *count += 1;
            LnIdent::from_ref(&format!("h{}", count), db)
        }
        None => {
            disambiguator_map.insert((namespace, "h".to_string()), 0);
            LnIdent::from_ref("h", db)
        }
    }
}

fn new_derivation_ident(
    disambiguator_map: &mut DisambiguatorMap,
    namespace: LnNamespace,
    db: &EternerDb,
) -> LnIdent {
    match disambiguator_map.get_mut(&(namespace, "d".to_string())) {
        Some(count) => {
            *count += 1;
            LnIdent::from_ref(&format!("d{}", count), db)
        }
        None => {
            disambiguator_map.insert((namespace, "d".to_string()), 0);
            LnIdent::from_ref("d", db)
        }
    }
}

fn naive_ident(head: &VdMirSymbolLocalDefnHead) -> String {
    match *head {
        VdMirSymbolLocalDefnHead::Letter(letter) => letter.to_string(),
    }
}

fn mangle_naive_ident(
    namespace: LnNamespace,
    naive_ident: String,
    disambiguator_map: &mut FxHashMap<(LnNamespace, String), usize>,
    db: &EternerDb,
) -> LnIdent {
    // If the identifier hasn't been used before, use it as-is
    let mangled = if !disambiguator_map.contains_key(&(namespace, naive_ident.clone())) {
        disambiguator_map.insert((namespace, naive_ident.clone()), 0);
        naive_ident
    } else {
        // Get the next number in sequence and increment it
        let next_num = disambiguator_map
            .get(&(namespace, naive_ident.clone()))
            .unwrap()
            + 1;
        disambiguator_map.insert((namespace, naive_ident.clone()), next_num);
        format!("{}{}", naive_ident, next_num)
    };

    LnIdent::from_owned(mangled, db)
}

#[test]
fn test_mangle_naive_ident() {
    use expect_test::expect;
    let db = &EternerDb::default();
    let mut disambiguator_map = FxHashMap::default();

    // First occurrence should be unchanged
    let root = LnNamespace::new_root(db);
    let result1 = mangle_naive_ident(root, "x".to_string(), &mut disambiguator_map, db);
    expect!["x"].assert_eq(&result1.data());

    // Second occurrence should be x1
    let result2 = mangle_naive_ident(root, "x".to_string(), &mut disambiguator_map, db);
    expect!["x1"].assert_eq(&result2.data());

    // Third occurrence should be x2
    let result3 = mangle_naive_ident(root, "x".to_string(), &mut disambiguator_map, db);
    expect!["x2"].assert_eq(&result3.data());

    // Different letter should start fresh
    let result4 = mangle_naive_ident(root, "y".to_string(), &mut disambiguator_map, db);
    expect!["y"].assert_eq(&result4.data());

    // Second occurrence of y should be y1
    let result5 = mangle_naive_ident(root, "y".to_string(), &mut disambiguator_map, db);
    expect!["y1"].assert_eq(&result5.data());
}
