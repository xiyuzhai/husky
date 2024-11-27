pub mod application;

use application::LnMirFunc;
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use lean_entity_path::LnItemPath;
use lean_opr::{
    opr::{binary::LnBinaryOpr, prefix::LnPrefixOpr, suffix::LnSuffixOpr},
    precedence::LnPrecedence,
};
use lean_term::term::literal::LnLiteral;
use smallvec::SmallVec;

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
    Sorry,
}

pub type LnMirExprArena = Arena<LnMirExprData>;
pub type LnMirExprArenaRef<'a> = ArenaRef<'a, LnMirExprData>;
pub type LnMirExprIdx = ArenaIdx<LnMirExprData>;
pub type LnMirExprIdxRange = ArenaIdxRange<LnMirExprData>;

impl LnMirExprData {
    pub(crate) fn outer_precedence(&self) -> LnPrecedence {
        match self {
            LnMirExprData::ItemPath(_)
            | LnMirExprData::Variable { .. }
            | LnMirExprData::Literal(_)
            | LnMirExprData::Sorry => LnPrecedence::Atom,
            // LnMirExprData::Prefix { opr, opd } => todo!(),
            // LnMirExprData::Suffix { opd, opr } => todo!(),
            // LnMirExprData::Binary { lopd, opr, ropd } => opr.outer_precedence(),
            LnMirExprData::Lambda { parameters, body } => todo!(),
            LnMirExprData::Application {
                function,
                arguments,
            } => function.outer_precedence(),
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
