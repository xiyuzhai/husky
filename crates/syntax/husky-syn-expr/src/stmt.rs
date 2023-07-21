mod error;
mod loop_stmt;

pub use error::*;
pub use loop_stmt::*;

use crate::*;
use husky_token::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange};

pub type StmtArena = Arena<Stmt>;
pub type StmtIdx = ArenaIdx<Stmt>;
pub type StmtIdxRange = ArenaIdxRange<Stmt>;
pub type StmtMap<V> = ArenaMap<Stmt, V>;

#[derive(Debug, PartialEq, Eq)]
#[salsa::derive_debug_with_db(db = ExprDb)]
pub enum Stmt {
    Let {
        let_token: LetToken,
        let_variable_pattern: ExprResult<LetVariableDecls>,
        assign_token: ExprResult<EqToken>,
        initial_value: ExprIdx,
    },
    Return {
        return_token: ReturnToken,
        result: ExprIdx,
    },
    Require {
        require_token: RequireToken,
        condition: ExprIdx,
    },
    Assert {
        assert_token: AssertToken,
        condition: ExprIdx,
    },
    Break {
        break_token: BreakToken,
    },
    Eval {
        expr_idx: ExprIdx,
    },
    ForBetween {
        for_token: StmtForToken,
        particulars: ForBetweenParticulars,
        frame_var_symbol_idx: CurrentSymbolIdx,
        eol_colon: ExprResult<EolToken>,
        block: ExprResult<StmtIdxRange>,
    },
    ForIn {
        for_token: StmtForToken,
        condition: ExprResult<ExprIdx>,
        eol_colon: ExprResult<EolToken>,
        block: ExprResult<StmtIdxRange>,
    },
    ForExt {
        forext_token: ForextToken,
        expr: ExprIdx,
        eol_colon: ExprResult<EolToken>,
        block: ExprResult<StmtIdxRange>,
    },
    While {
        while_token: WhileToken,
        condition: ExprResult<ExprIdx>,
        eol_colon: ExprResult<EolToken>,
        block: ExprResult<StmtIdxRange>,
    },
    DoWhile {
        do_token: DoToken,
        while_token: WhileToken,
        condition: ExprResult<ExprIdx>,
        eol_colon: ExprResult<EolToken>,
        block: ExprResult<StmtIdxRange>,
    },
    IfElse {
        if_branch: IfBranch,
        elif_branches: Vec<ElifBranch>,
        else_branch: Option<ElseBranch>,
    },
    Match {
        match_token: MatchToken,
    },
    Err(StmtError),
}

impl From<StmtResult<Stmt>> for Stmt {
    fn from(value: StmtResult<Stmt>) -> Self {
        match value {
            Ok(stmt) => stmt,
            Err(err) => Stmt::Err(err),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IfBranch {
    pub if_token: IfToken,
    pub condition: ExprResult<ExprIdx>,
    pub eol_colon: ExprResult<EolToken>,
    pub block: ExprResult<StmtIdxRange>,
}

impl IfBranch {
    pub fn condition(&self) -> Result<&ExprIdx, &ExprError> {
        self.condition.as_ref()
    }

    pub fn eol_colon_token(&self) -> Result<&EolToken, &ExprError> {
        self.eol_colon.as_ref()
    }

    pub fn block(&self) -> Result<StmtIdxRange, &ExprError> {
        self.block.as_ref().copied()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ElifBranch {
    pub elif_token: ElifToken,
    pub condition: ExprResult<ExprIdx>,
    pub eol_colon: ExprResult<EolToken>,
    pub block: ExprResult<StmtIdxRange>,
}

impl ElifBranch {
    pub fn condition(&self) -> Result<&ExprIdx, &ExprError> {
        self.condition.as_ref()
    }

    pub fn eol_colon(&self) -> Result<&EolToken, &ExprError> {
        self.eol_colon.as_ref()
    }

    pub fn block(&self) -> Result<StmtIdxRange, &ExprError> {
        self.block.as_ref().copied()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ElseBranch {
    pub else_token: ElseToken,
    pub eol_colon: ExprResult<EolToken>,
    pub block: ExprResult<StmtIdxRange>,
}

impl ElseBranch {
    pub fn block(&self) -> Result<StmtIdxRange, &ExprError> {
        self.block.as_ref().copied()
    }
}