use super::*;
use parsec::{HasStreamState, IsStreamParser};

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(crate) fn parse_closure(
        &mut self,
        lvert_regional_token_idx: RegionalTokenIdx,
    ) -> SynExprResult<SynExprData> {
        let parameters: PunctuatedSmallList<
            ClosureParameterSyndicate,
            CommaRegionalToken,
            SynExprError,
            true,
            3,
        > = self.try_parse()?;
        let rvert_regional_token =
            self.try_parse_expected(OriginalSynExprError::ExpectedRvertForClosure)?;
        let light_arrow_token: Option<LightArrowRegionalToken> = self.try_parse_option()?;
        let return_ty = match light_arrow_token {
            Some(light_arrow_token) => {
                let return_ty = self.parse_expr_expected(
                    None,
                    OriginalSynExprError::ExpectedReturnTypeAfterLightArrowForClosure,
                )?;
                let eq_token = self.try_parse_expected(
                    OriginalSynExprError::ExpectedEqTokenAfterReturnTypeForClosure,
                )?;
                Some((light_arrow_token, return_ty, eq_token))
            }
            None => None,
        };
        let body =
            self.parse_expr_expected(None, OriginalSynExprError::ExpectedBodyExprForClosure)?;
        let access_end = RegionalTokenIdxRangeEnd::new_abstract_variables_access_end(self.state());
        for param in parameters.elements() {
            match param {
                ClosureParameterSyndicate::Simple { variables, .. } => {
                    for var in variables {
                        self.context_mut()
                            .set_abstract_variable_access_end(var, access_end)
                    }
                }
            }
        }
        Ok(SynExprData::Closure {
            closure_kind_regional_token_idx: None,
            lvert_regional_token_idx,
            parameters,
            rvert_regional_token,
            return_ty,
            body,
        })
    }
}
