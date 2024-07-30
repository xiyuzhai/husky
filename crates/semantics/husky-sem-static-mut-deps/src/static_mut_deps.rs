use husky_entity_path::path::ItemPath;
use vec_like::OrderedSmallVecSet;

#[salsa::derive_debug_with_db]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SemStaticMutDeps(OrderedSmallVecSet<ItemPath, 4>);

impl SemStaticMutDeps {
    pub(crate) fn merge(&mut self, other: &[ItemPath]) {
        self.0.extend(other);
    }

    pub(crate) fn merge_counted(&mut self, other: &Self, counter: &mut EffectiveMergeCounter) {
        let old_len = self.0.len();
        self.0.extend(&other.0);
        if old_len != self.0.len() {
            counter.count += 1
        }
    }

    pub(crate) fn insert(&mut self, item_path: ItemPath) {
        self.0.insert(item_path);
    }
}

/// None indicates no control flow
#[salsa::derive_debug_with_db]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SemControlFlowStaticMutDeps(Option<OrderedSmallVecSet<ItemPath, 4>>);

#[test]
fn sem_control_flow_static_var_deps_default_works() {
    assert_eq!(
        SemControlFlowStaticMutDeps::default(),
        SemControlFlowStaticMutDeps(None)
    );
}

impl SemControlFlowStaticMutDeps {
    /// a deps that represents a control flow that happens without any dependencies
    pub(crate) fn new_empty() -> Self {
        Self(Some(Default::default()))
    }
}

impl std::ops::Deref for SemControlFlowStaticMutDeps {
    type Target = [ItemPath];

    fn deref(&self) -> &Self::Target {
        match self.0 {
            Some(ref deps) => deps,
            None => &[],
        }
    }
}

impl SemControlFlowStaticMutDeps {
    pub(crate) fn merge(&mut self, other: &Self) {
        match self.0 {
            Some(ref mut slf) => slf.extend(other),
            None => match other.0 {
                Some(ref other) => self.0 = Some(other.clone()),
                None => (),
            },
        }
    }

    /// use this when some control flow is caused by the value
    ///
    /// this will result in .0 always being Some
    pub(crate) fn merge_with_value(&mut self, other: &SemStaticMutDeps) {
        match self.0 {
            Some(ref mut slf) => slf.extend(other),
            None => self.0 = Some(other.0.clone()),
        }
    }

    pub(crate) fn compose_with_value(&mut self, other: &SemStaticMutDeps) {
        match self.0 {
            Some(ref mut slf) => slf.extend(other),
            None => (), // doing nothing because if the thing doesn't have a control flow, so does its conditional version
        }
    }

    /// this is used when caching, to see whether there is any effective change
    pub(crate) fn merge_counted(&mut self, other: &Self, counter: &mut EffectiveMergeCounter) {
        match self.0 {
            Some(ref mut slf) => {
                let old_len = slf.len();
                slf.extend(other);
                if old_len != slf.len() {
                    counter.count += 1;
                }
            }
            None => match other.0 {
                Some(ref _other) => {
                    unreachable!("for the circumstance this function is going to be invoked, this case will not happen")
                    // self.0 = Some(other.clone());
                    // counter.count += 1;
                }
                None => (),
            },
        }
    }
}

#[derive(Default)]
pub(crate) struct EffectiveMergeCounter {
    count: usize,
}

impl EffectiveMergeCounter {
    pub fn count(&self) -> usize {
        self.count
    }
}

impl std::ops::Deref for SemStaticMutDeps {
    type Target = OrderedSmallVecSet<ItemPath, 4>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl IntoIterator for &SemStaticMutDeps {
    type Item = ItemPath;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().copied()
    }
}