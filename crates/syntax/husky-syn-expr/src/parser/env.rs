use super::*;
use husky_token_data::delimiter::Delimiter;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprEnvironment {
    TypeBeforeEq,
    WithinDelimiteredParameterList(Delimiter),
    /// the range end is for pattern variables in the condition
    Condition(RegionalTokenIdxRangeEnd),
}

pub struct ExprEnvironmentStack(smallvec::SmallVec<[ExprEnvironment; 2]>);

impl ExprEnvironmentStack {
    pub(super) fn new(env: Option<ExprEnvironment>) -> Self {
        ExprEnvironmentStack(env.into_iter().collect())
    }

    pub(super) fn set(&mut self, env: ExprEnvironment) {
        self.0.push(env)
    }

    pub(super) fn unset(&mut self) {
        self.0.pop().expect("len() > 0");
    }
}

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(super) fn env(&self) -> Option<ExprEnvironment> {
        self.env_stack.0.last().copied()
    }
    pub(super) fn env_bra(&self) -> Option<Delimiter> {
        match self.env()? {
            ExprEnvironment::WithinDelimiteredParameterList(bra) => Some(bra),
            ExprEnvironment::TypeBeforeEq => None,
            ExprEnvironment::Condition(_) => None,
        }
    }
}
