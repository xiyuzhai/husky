use repl::ReplSource;

use crate::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct VariableRegionData {
    inherited_variable_arena: InheritedVariableArena,
    current_variable_arena: CurrentVariableArena,
    allow_self_type: AllowSelfType,
    allow_self_value: AllowSelfValue,
    pattern_ty_constraints: Vec<(SyndicateTypeConstraint, CurrentVariableIdxRange)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AllowSelfValue {
    True,
    False,
}

impl AllowSelfValue {
    pub fn to_bool(self) -> bool {
        match self {
            AllowSelfValue::True => true,
            AllowSelfValue::False => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AllowSelfType {
    True,
    False,
}

impl AllowSelfType {
    pub fn to_bool(self) -> bool {
        match self {
            AllowSelfType::True => true,
            AllowSelfType::False => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SyndicateTypeConstraint {
    TemplateTypeParameter,
    SimpleParenateParameter {
        syn_pattern_root: ParenateParameterSynPatternRoot,
        ty: SynExprIdx,
    },
    VariadicParenateParameter {
        ident_token: IdentRegionalToken,
        ty: SynExprIdx,
    },
    SimpleClosureParameter {
        syn_pattern_root: ClosureSynPatternRoot,
        ty: SynExprIdx,
    },
    LetPattern {
        pattern: LetPatternSynExprRoot,
        ty: SynExprIdx,
    },
    FieldVariable {
        ident_token: IdentRegionalToken,
        ty_expr_idx: SynExprIdx,
    },
    LoopVariable,
}

impl VariableRegionData {
    /// # constructor
    pub(crate) fn new(
        parent_symbol_region: Option<&VariableRegionData>,
        allow_self_type: AllowSelfType,
        allow_self_value: AllowSelfValue,
        repl_src: Option<ReplSource>,
    ) -> Self {
        #[cfg(test)]
        {
            if allow_self_value.to_bool() {
                assert!(allow_self_type.to_bool());
            } else {
                if let Some(parent_symbol_region) = parent_symbol_region {
                    assert!(!parent_symbol_region.allow_self_value.to_bool());
                }
            }
            if !allow_self_type.to_bool() {
                if let Some(parent_symbol_region) = parent_symbol_region {
                    assert!(!parent_symbol_region.allow_self_type.to_bool());
                }
            }
        }
        Self {
            inherited_variable_arena: match parent_symbol_region {
                Some(parent_symbol_region) => parent_symbol_region.bequeath(repl_src),
                None => Default::default(),
            },
            current_variable_arena: Default::default(),
            allow_self_type,
            allow_self_value,
            pattern_ty_constraints: vec![],
        }
    }

    /// # actions

    #[inline(always)]
    pub(crate) fn define_symbol(
        &mut self,
        variable: CurrentVariableEntry,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdx {
        let symbol = self.current_variable_arena.alloc_one(variable);
        self.pattern_ty_constraints.extend(
            ty_constraint
                .into_iter()
                .map(|ty_constraint| (ty_constraint, CurrentVariableIdxRange::new_single(symbol))),
        );
        symbol
    }

    #[inline(always)]
    pub(crate) fn define_variables(
        &mut self,
        variables: impl IntoIterator<Item = CurrentVariableEntry>,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdxRange {
        let symbols = self.current_variable_arena.alloc_batch(variables);
        self.pattern_ty_constraints.extend(
            ty_constraint
                .into_iter()
                .map(|ty_constraint| (ty_constraint, symbols)),
        );
        symbols
    }

    pub(super) fn set_abstract_variable_access_end(
        &mut self,
        var: CurrentVariableIdx,
        access_end: RegionalTokenIdxRangeEnd,
    ) {
        self.current_variable_arena.update(var, |entry| {
            debug_assert!(entry.access_end.is_none());
            entry.access_end = Some(access_end)
        })
    }

    /// # queries

    pub(crate) fn resolve_ident(
        &self,
        regional_token_idx: RegionalTokenIdx,
        ident: Ident,
    ) -> Option<Symbol> {
        self.current_variable_arena
            .find_rev_indexed(|symbol| {
                let accessible = match symbol.access_end {
                    Some(access_end) => access_end.regional_token_idx() > regional_token_idx,
                    None => true,
                };
                symbol.ident() == Some(ident) && accessible
            })
            .map(|(current_variable_idx, current_variable)| {
                Symbol::Current(current_variable_idx, current_variable.kind())
            })
            .or_else(|| {
                self.inherited_variable_arena
                    .find_rev_indexed(|symbol| symbol.ident() == Some(ident))
                    .map(|(inherited_variable_idx, inherited_variable)| {
                        Symbol::Inherited(inherited_variable_idx, inherited_variable.kind)
                    })
            })
    }

    pub fn inherited_variables<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'a InheritedVariableEntry> + 'a {
        self.inherited_variable_arena.data().iter()
    }

    pub fn indexed_inherited_variables<'a>(
        &'a self,
    ) -> impl Iterator<Item = (InheritedVariableIdx, InheritedVariableEntry)> + 'a {
        self.inherited_variable_arena.indexed_copy_iter()
    }

    pub fn current_variables<'a>(&'a self) -> impl Iterator<Item = &'a CurrentVariableEntry> + 'a {
        self.current_variable_arena.iter()
    }

    pub fn indexed_current_variables<'a>(
        &'a self,
    ) -> impl Iterator<Item = (CurrentVariableIdx, &'a CurrentVariableEntry)> + 'a {
        self.current_variable_arena.indexed_iter()
    }

    pub fn current_variable_indices(&self) -> impl Iterator<Item = CurrentVariableIdx> {
        self.current_variable_arena.indices()
    }

    /// todo: needs overhaul for repl trace
    ///
    /// add an argument for repl insertion position (RegionalTokenIdx)
    fn bequeath(&self, repl_src: Option<ReplSource>) -> InheritedVariableArena {
        let mut inherited_variable_arena = InheritedVariableArena::default();
        for (_, inherited_variable_entry) in self.indexed_inherited_variables() {
            inherited_variable_arena.alloc_one(inherited_variable_entry);
        }
        for (current_variable_idx, current_variable) in self.indexed_current_variables() {
            if repl_src.is_some() {
                todo!("filter out those inaccessible for the `repl_src`")
            }
            let kind = match current_variable.data {
                CurrentVariableData::SimpleParenateParameter { ident, .. } => {
                    // should we add `InheritedVariableKind::ReplParenate`?
                    InheritedVariableKind::Parenate { ident }
                }
                CurrentVariableData::LetVariable { .. }
                | CurrentVariableData::BeVariable { .. }
                | CurrentVariableData::CaseVariable { .. }
                | CurrentVariableData::LoopVariable { .. }
                | CurrentVariableData::SelfValue { .. }
                | CurrentVariableData::SimpleClosureParameter { .. } => {
                    // we should only encounter these cases when processing repl traces
                    debug_assert!(repl_src.is_some());
                    InheritedVariableKind::ReplLocal
                }
                CurrentVariableData::TemplateParameter { ref data, .. } => {
                    InheritedVariableKind::Template(data.bequeath())
                }
                CurrentVariableData::VariadicParenateParameter { ident_token, .. } => {
                    InheritedVariableKind::Parenate {
                        ident: ident_token.ident(),
                    }
                }
                CurrentVariableData::SelfType => unreachable!(),
                CurrentVariableData::FieldVariable { ident_token } => {
                    InheritedVariableKind::SelfField {
                        ident: ident_token.ident(),
                    }
                }
            };
            let modifier = current_variable.modifier;
            inherited_variable_arena.alloc_one(InheritedVariableEntry { kind, modifier });
        }
        inherited_variable_arena
    }

    pub fn allow_self_ty(&self) -> AllowSelfType {
        self.allow_self_type
    }

    pub fn allow_self_value(&self) -> AllowSelfValue {
        self.allow_self_value
    }

    pub fn inherited_variable_arena(&self) -> &InheritedVariableArena {
        &self.inherited_variable_arena
    }

    pub fn current_variable_arena(&self) -> &CurrentVariableArena {
        &self.current_variable_arena
    }

    pub fn pattern_ty_constraints(&self) -> &[(SyndicateTypeConstraint, CurrentVariableIdxRange)] {
        &self.pattern_ty_constraints
    }
}

impl std::ops::Index<InheritedVariableIdx> for VariableRegionData {
    type Output = InheritedVariableEntry;

    fn index(&self, index: InheritedVariableIdx) -> &Self::Output {
        &self.inherited_variable_arena[index]
    }
}

impl std::ops::Index<CurrentVariableIdx> for VariableRegionData {
    type Output = CurrentVariableEntry;

    fn index(&self, index: CurrentVariableIdx) -> &Self::Output {
        &self.current_variable_arena[index]
    }
}

pub enum Prevariable {}

/// equal to InheritedVariableIdx
///
/// equal to CurrentVariableIdx + number of inherited symbols
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LocalSymbolIdx(usize);

impl From<InheritedVariableIdx> for LocalSymbolIdx {
    fn from(value: InheritedVariableIdx) -> Self {
        Self(value.index())
    }
}

impl LocalSymbolIdx {
    fn from_current_variable_idx(
        current_variable_idx: CurrentVariableIdx,
        symbol_region: &VariableRegionData,
    ) -> Self {
        Self(symbol_region.inherited_variable_arena.len() + current_variable_idx.index())
    }
}

pub trait IntoLocalSymbolIdx: Copy {
    fn into_local_symbol_idx(self, expr_region_data: &SynExprRegionData) -> LocalSymbolIdx;
}

impl IntoLocalSymbolIdx for InheritedVariableIdx {
    fn into_local_symbol_idx(self, _: &SynExprRegionData) -> LocalSymbolIdx {
        self.into()
    }
}

impl IntoLocalSymbolIdx for CurrentVariableIdx {
    fn into_local_symbol_idx(self, expr_region_data: &SynExprRegionData) -> LocalSymbolIdx {
        LocalSymbolIdx::from_current_variable_idx(self, expr_region_data.variable_region())
    }
}
