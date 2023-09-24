use parsec::HasStreamState;

use super::*;

#[derive(Debug, PartialEq, Eq)]
#[salsa::debug_with_db(db = EntitySynTreeDb)]
pub struct LetPatternObelisk {
    syn_pattern_root: SynPatternRoot,
    variables: CurrentSynSymbolIdxRange,
    colon_token: SynExprResult<Option<ColonRegionalToken>>,
    ty: Option<SynExprIdx>,
}

impl<'a, 'b> SynDefnExprParser<'a, 'b> {
    pub(crate) fn parse_let_variables_pattern_expected(
        &mut self,
        access_end: RegionalTokenIdxRangeEnd,
    ) -> SynExprResult<LetPatternObelisk> {
        let state = self.save_state();
        let Some(syn_pattern_root) = self.try_parse_option()? else {
            Err(OriginalSynExprError::ExpectedLetPattern(state))?
        };
        let symbols = self
            .pattern_expr_region()
            .pattern_expr_symbols(syn_pattern_root);
        let access_start = self.save_state().next_regional_token_idx();
        let symbols = symbols
            .iter()
            .map(|(ident, pattern_symbol)| {
                CurrentSynSymbol::new(
                    self.pattern_expr_region(),
                    access_start,
                    Some(access_end),
                    CurrentSynSymbolVariant::LetVariable {
                        ident: *ident,
                        pattern_symbol_idx: *pattern_symbol,
                    },
                )
            })
            .collect::<Vec<_>>();
        let colon_token = self
            .try_parse_option::<ColonRegionalToken>()
            .map_err(|e| e.into());
        let ty = match colon_token {
            Ok(Some(_)) => Some(self.parse_expr_expected2(
                Some(ExprEnvironment::TypeBeforeEq),
                ExprRootKind::LetStmtType,
                OriginalSynExprError::ExpectedLetVariablesType,
            )),
            _ => None,
        };
        let ty_constraint = ty.map(|ty| ObeliskTypeConstraint::LetPattern {
            pattern: syn_pattern_root,
            ty,
        });
        let variables = self.define_symbols(symbols, ty_constraint);
        Ok(LetPatternObelisk {
            syn_pattern_root,
            variables,
            colon_token,
            ty,
        })
    }
}

impl LetPatternObelisk {
    pub fn syn_pattern_root(&self) -> SynPatternRoot {
        self.syn_pattern_root
    }

    pub fn ty(&self) -> Option<SynExprIdx> {
        self.ty
    }

    pub fn variables(&self) -> CurrentSynSymbolIdxRange {
        self.variables
    }
}