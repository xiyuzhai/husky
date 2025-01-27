pub mod application;

use application::LnMirFunc;
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use lean_entity_path::LnItemPath;
use lean_opr::{
    opr::{binary::LnBinaryOpr, prefix::LnPrefixOpr, suffix::LnSuffixOpr},
    precedence::LnPrecedence,
};
use lean_term::{
    term::literal::{LnLiteral, LnLiteralData},
    ty::LnType,
};
use smallvec::SmallVec;

use crate::tactic::LnMirTacticIdxRange;

#[derive(Debug, PartialEq, Eq)]
pub enum LnMirExprData {
    Literal(LnLiteral),
    ItemPath(LnItemPath),
    Variable {
        ident: LnIdent,
    },
    Lambda {
        parameters: LnMirLambdaParameters,
        body: LnMirExprIdx,
    },
    Application {
        function: LnMirFunc,
        arguments: LnMirExprIdxRange,
    },
    TypeAscription {
        expr: LnMirExprIdx,
        ty: LnMirExprIdx,
    },
    By {
        tactics: LnMirTacticIdxRange,
    },
    Sorry,
}

pub struct LnMirExprEntry {
    data: LnMirExprData,
}

pub type LnMirExprArena = Arena<LnMirExprEntry>;
pub type LnMirExprArenaRef<'a> = ArenaRef<'a, LnMirExprEntry>;
pub type LnMirExprIdx = ArenaIdx<LnMirExprEntry>;
pub type LnMirExprIdxRange = ArenaIdxRange<LnMirExprEntry>;

impl LnMirExprEntry {
    pub fn new(data: LnMirExprData) -> Self {
        Self { data }
    }
}

impl LnMirExprEntry {
    pub fn data(&self) -> &LnMirExprData {
        &self.data
    }
}

impl LnMirExprData {
    pub(crate) fn outer_precedence(&self) -> LnPrecedence {
        match self {
            LnMirExprData::ItemPath(_) | LnMirExprData::Variable { .. } | LnMirExprData::Sorry => {
                LnPrecedence::ATOM
            }
            LnMirExprData::Literal(lit) => match lit.data() {
                LnLiteralData::Nat(_) => LnPrecedence::ATOM,
                LnLiteralData::Int(i) => {
                    if i.starts_with("-") {
                        LnPrecedence::NEG
                    } else {
                        LnPrecedence::ATOM
                    }
                }
                LnLiteralData::Frac(_) => LnPrecedence::MUL_DIV,
            },
            LnMirExprData::Lambda { parameters, body } => todo!(),
            LnMirExprData::Application {
                function,
                arguments,
            } => function.outer_precedence(),
            LnMirExprData::By { tactics } => LnPrecedence::Min,
            LnMirExprData::TypeAscription { expr, ty } => todo!(),
        }
    }

    pub(crate) fn children(&self) -> Vec<LnMirExprIdx> {
        match *self {
            LnMirExprData::ItemPath(_)
            | LnMirExprData::Literal(_)
            | LnMirExprData::Sorry
            | LnMirExprData::Variable { .. } => vec![],
            LnMirExprData::Lambda {
                ref parameters,
                body,
            } => todo!(),
            LnMirExprData::Application {
                function,
                arguments,
            } => function.expr().into_iter().chain(arguments).collect(),
            LnMirExprData::By { tactics } => todo!(),
            LnMirExprData::TypeAscription { expr, ty } => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LnMirLambdaParameter {
    ident: LnIdent,
    ty: LnMirExprIdx,
}

impl LnMirLambdaParameter {
    pub fn ident(&self) -> LnIdent {
        self.ident
    }

    pub fn ty(&self) -> LnMirExprIdx {
        self.ty
    }
}

pub type LnMirLambdaParameters = SmallVec<[LnMirLambdaParameter; 4]>;
