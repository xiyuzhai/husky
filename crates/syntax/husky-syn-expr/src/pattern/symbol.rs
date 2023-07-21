use idx_arena::ordered_map::ArenaOrderedMap;

use super::*;

#[derive(Debug, PartialEq, Eq)]
#[salsa::derive_debug_with_db(db = ExprDb)]
pub enum PatternSymbol {
    Atom(PatternExprIdx),
}

impl PatternSymbol {
    pub(super) fn pattern_symbol_modifier(
        &self,
        pattern_expr_arena: &PatternExprArena,
    ) -> SymbolModifier {
        match self {
            PatternSymbol::Atom(expr_idx) => match pattern_expr_arena[*expr_idx] {
                PatternExpr::Ident {
                    symbol_modifier_keyword_group,
                    ident_token,
                } => SymbolModifier::new(symbol_modifier_keyword_group),
                _ => unreachable!(),
            },
        }
    }
}

pub type PatternSymbolArena = Arena<PatternSymbol>;
pub type PatternSymbolIdx = ArenaIdx<PatternSymbol>;
pub type PatternSymbolMap<V> = ArenaMap<PatternSymbol, V>;
pub type PatternSymbolOrderedMap<V> = ArenaOrderedMap<PatternSymbol, V>;