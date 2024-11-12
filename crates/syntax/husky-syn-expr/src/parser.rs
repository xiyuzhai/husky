mod accept;
mod debug;
mod disambiguate_token;
mod env;
mod expr_stack;
pub(crate) mod incomplete_expr;

pub use self::env::*;

pub(crate) use self::disambiguate_token::*;

use self::expr_stack::*;
use self::incomplete_expr::*;
use crate::variable::*;
use crate::*;
use husky_opr::precedence::*;
use original_error::OriginalError;
use parsec::{HasStreamState, IsStreamParser};
use std::ops::ControlFlow;

/// parse token group into exprs
pub struct SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(crate) context: C,
    env_stack: ExprEnvironmentStack,
    token_stream: RegionalTokenStream<'a>,
    stack: SynExprStack,
}

pub type StandaloneSynExprParser<'a> = SynExprParser<'a, SynExprContext<'a>>;
pub type ProducedSynExprParser<'a, 'b> = SynExprParser<'a, &'b mut SynExprContext<'a>>;

impl<'a, C> ::salsa::db::HasDb<'a> for SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    fn db(&self) -> &'a ::salsa::Db {
        self.context().db()
    }
}

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(super) fn new(
        context: C,
        env: Option<ExprEnvironment>,
        token_stream: RegionalTokenStream<'a>,
    ) -> Self {
        Self {
            context,
            env_stack: ExprEnvironmentStack::new(env),
            token_stream,
            stack: Default::default(),
        }
    }

    pub(crate) fn context(&self) -> &SynExprContext<'a> {
        self.context.borrow()
    }

    pub(crate) fn context_mut(&mut self) -> &mut SynExprContext<'a> {
        self.context.borrow_mut()
    }

    pub fn db(&self) -> &'a ::salsa::Db {
        self.context().db()
    }

    pub fn syn_expr_arena(&self) -> &SynExprArena {
        &self.context().syn_expr_arena()
    }

    pub fn parse_expr_root(
        &mut self,
        env: impl Into<Option<ExprEnvironment>>,
        expr_root_kind: SynExprRootKind,
    ) -> Option<SynExprIdx> {
        let env = env.into();
        if let Some(env) = env {
            self.env_stack.set(env);
        }
        loop {
            let Some((regional_token_idx, token_data)) = self.token_stream.next_indexed() else {
                break;
            };
            match self.disambiguate_token(regional_token_idx, token_data) {
                ControlFlow::Continue(resolved_token) => self.accept_token(resolved_token),
                ControlFlow::Break(_) => {
                    self.rollback_raw(regional_token_idx);
                    break;
                }
            }
        }
        self.reduce(Precedence::None);
        if env.is_some() {
            self.env_stack.unset();
        }
        let opt_expr_idx = self.finish_batch();
        opt_expr_idx.map(|expr_idx| self.context_mut().add_expr_root(expr_root_kind, expr_idx));
        opt_expr_idx
    }

    pub fn parse_expr_expected<E: OriginalError>(
        &mut self,
        env: Option<ExprEnvironment>,
        err: impl FnOnce(RegionalTokenStreamState) -> E,
    ) -> Result<SynExprIdx, E::Error> {
        let state = self.state();
        if let Some(env) = env {
            self.env_stack.set(env);
        }
        loop {
            let Some((token_idx, token)) = self.token_stream.next_indexed() else {
                break;
            };
            match self.disambiguate_token(token_idx, token) {
                ControlFlow::Continue(resolved_token) => self.accept_token(resolved_token),
                ControlFlow::Break(_) => {
                    self.rollback_raw(token_idx);
                    break;
                }
            }
        }
        self.reduce(Precedence::None);
        if env.is_some() {
            self.env_stack.unset();
        }
        match self.finish_batch() {
            Some(expr_idx) => Ok(expr_idx),
            None => Err(err(state).into()),
        }
    }

    pub fn parse_expr_expected2(
        &mut self,
        env: Option<ExprEnvironment>,
        expr_root_kind: impl Into<Option<SynExprRootKind>>,
        err: impl FnOnce(RegionalTokenStreamState) -> OriginalSynExprError,
    ) -> SynExprIdx {
        let state = self.state();
        if let Some(env) = env {
            self.env_stack.set(env);
        }
        loop {
            let Some((token_idx, token)) = self.token_stream.next_indexed() else {
                break;
            };
            match self.disambiguate_token(token_idx, token) {
                ControlFlow::Continue(resolved_token) => self.accept_token(resolved_token),
                ControlFlow::Break(_) => {
                    self.rollback_raw(token_idx);
                    break;
                }
            }
        }
        self.reduce(Precedence::None);
        if env.is_some() {
            self.env_stack.unset();
        }
        let expr_idx = {
            match self.finish_batch() {
                Some(expr_idx) => expr_idx,
                None => self
                    .context_mut()
                    .alloc_expr(SynExprData::Err(err(state).into())),
            }
        };
        if let Some(expr_root_kind) = expr_root_kind.into() {
            self.context_mut().add_expr_root(expr_root_kind, expr_idx);
        }
        expr_idx
    }

    pub(crate) fn pattern_region(&self) -> &SynPatternRegion {
        self.context().pattern_region()
    }

    pub(crate) fn define_symbol(
        &mut self,
        variable: CurrentVariableEntry,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdx {
        self.context_mut().define_symbol(variable, ty_constraint)
    }

    pub(crate) fn define_symbols(
        &mut self,
        variables: impl IntoIterator<Item = CurrentVariableEntry>,
        ty_constraint: Option<SyndicateTypeConstraint>,
    ) -> CurrentVariableIdxRange {
        self.context_mut().define_symbols(variables, ty_constraint)
    }

    fn allow_self_ty(&self) -> AllowSelfType {
        self.context()
            .variable_context()
            .symbol_region()
            .allow_self_ty()
    }

    fn allow_self_value(&self) -> AllowSelfValue {
        self.context()
            .variable_context()
            .symbol_region()
            .allow_self_value()
    }
}

impl<'a> SynExprParser<'a, SynExprContext<'a>> {
    pub fn finish(self) -> SynExprRegion {
        self.context.finish()
    }
}

impl<'a, C> std::ops::Deref for SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    type Target = RegionalTokenStream<'a>;
    fn deref(&self) -> &Self::Target {
        &self.token_stream
    }
}

impl<'a, C> std::ops::DerefMut for SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.token_stream
    }
}

impl<'a, C> std::borrow::Borrow<RegionalTokenStream<'a>> for SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    fn borrow(&self) -> &RegionalTokenStream<'a> {
        &self.token_stream
    }
}

impl<'a, C> std::borrow::BorrowMut<RegionalTokenStream<'a>> for SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    fn borrow_mut(&mut self) -> &mut RegionalTokenStream<'a> {
        &mut self.token_stream
    }
}

impl<'a, C> parsec::StreamWrapper for SynExprParser<'a, C> where C: IsSynExprContext<'a> {}
