use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use lean_item_path::LnItemPath;
use lean_opr::{
    opr::{binary::LnBinaryOpr, prefix::LnPrefixOpr, suffix::LnSuffixOpr},
    precedence::LnPrecedence,
};
use lean_term::term::literal::LnLiteral;
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum LnHirExprData {
    Literal(LnLiteral),
    ItemPath(LnItemPath),
    Variable {
        ident: LnIdent,
    },
    Prefix {
        opr: LnPrefixOpr,
        opd: LnHirExprIdx,
    },
    Suffix {
        opd: LnHirExprIdx,
        opr: LnSuffixOpr,
    },
    Binary {
        lopd: LnHirExprIdx,
        opr: LnBinaryOpr,
        ropd: LnHirExprIdx,
    },
    Lambda {
        parameters: LnHirLambdaParameters,
        body: LnHirExprIdx,
    },
    Application {
        function_and_arguments: LnHirExprIdxRange,
    },
}

pub type LnHirExprArena = Arena<LnHirExprData>;
pub type LnHirExprArenaRef<'a> = ArenaRef<'a, LnHirExprData>;
pub type LnHirExprIdx = ArenaIdx<LnHirExprData>;
pub type LnHirExprIdxRange = ArenaIdxRange<LnHirExprData>;

impl LnHirExprData {
    pub(crate) fn outer_precedence(&self) -> LnPrecedence {
        match self {
            LnHirExprData::ItemPath(_) => LnPrecedence::Atom,
            LnHirExprData::Variable { ident } => todo!(),
            LnHirExprData::Prefix { opr, opd } => todo!(),
            LnHirExprData::Suffix { opd, opr } => todo!(),
            LnHirExprData::Binary { lopd, opr, ropd } => opr.outer_precedence(),
            LnHirExprData::Lambda { parameters, body } => todo!(),
            LnHirExprData::Application {
                function_and_arguments,
            } => todo!(),
            LnHirExprData::Literal(_) => LnPrecedence::Atom,
        }
    }

    pub(crate) fn children(&self) -> Vec<LnHirExprIdx> {
        match *self {
            LnHirExprData::ItemPath(_) | LnHirExprData::Literal(_) => vec![],
            LnHirExprData::Variable { ident } => todo!(),
            LnHirExprData::Prefix { opr, opd } => todo!(),
            LnHirExprData::Suffix { opd, opr } => todo!(),
            LnHirExprData::Binary { lopd, opr, ropd } => vec![lopd, ropd],
            LnHirExprData::Lambda {
                ref parameters,
                body,
            } => todo!(),
            LnHirExprData::Application {
                function_and_arguments,
            } => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LnHirLambdaParameter {
    ident: LnIdent,
    ty: LnHirExprIdx,
}

impl LnHirLambdaParameter {
    pub fn ident(&self) -> LnIdent {
        self.ident
    }

    pub fn ty(&self) -> LnHirExprIdx {
        self.ty
    }
}

pub type LnHirLambdaParameters = SmallVec<[LnHirLambdaParameter; 4]>;
