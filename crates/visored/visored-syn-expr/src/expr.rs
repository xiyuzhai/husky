pub mod attach;
pub mod binary;
pub mod letter;
pub mod list_item;
pub mod literal;
pub mod prefix;
pub mod suffix;
#[cfg(test)]
mod tests;
pub mod uniadic_array;
pub mod uniadic_chain;
pub mod variadic_array;
pub mod variadic_chain;

use crate::builder::{ToVdSyn, VdSynExprBuilder};
use crate::*;
use either::*;
use error::{OriginalVdSynExprError, VdSynExprError};
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use latex_ast::ast::{
    math::{LxMathAstData, LxMathAstIdx, LxMathAstIdxRange},
    LxAstIdxRange,
};
use latex_math_letter::letter::LxMathLetter;
use latex_prelude::script::LxScriptKind;
use latex_token::{
    data::math::LxMathDelimiter,
    idx::{LxMathTokenIdx, LxTokenIdx, LxTokenIdxRange},
};
use range::VdSynExprTokenIdxRange;
use smallvec::{smallvec, SmallVec};
use std::fmt::Formatter;
use symbol::{
    builder::VdSynSymbolBuilder,
    resolution::{
        error::VdSynSymbolResolutionResult, letter::VdSynLetterSymbolResolution,
        VdSynSymbolResolution, VdSynSymbolResolutions,
    },
};
use visored_opr::{
    delimiter::{
        VdBaseLeftDelimiter, VdBaseRightDelimiter, VdCompositeLeftDelimiter,
        VdCompositeRightDelimiter,
    },
    opr::{
        binary::{VdBaseBinaryOpr, VdCompositeBinaryOpr},
        prefix::{VdBasePrefixOpr, VdCompositePrefixOpr},
        suffix::{VdBaseSuffixOpr, VdCompositeSuffixOpr},
        VdBaseOpr,
    },
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::{VdBaseSeparator, VdSeparatorClass},
};
use visored_zfc_ty::term::literal::{VdZfcLiteral, VdZfcLiteralData};

/// It's a tree of both form and meaning
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum VdSynExprData {
    Literal {
        token_idx_range: LxTokenIdxRange,
        literal: VdZfcLiteral,
    },
    Letter {
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    },
    BaseOpr {
        opr: VdBaseOpr,
    },
    Binary {
        lopd: VdSynExprIdx,
        opr: VdSynBinaryOpr,
        ropd: VdSynExprIdx,
    },
    Prefix {
        opr: VdSynPrefixOpr,
        opd: VdSynExprIdx,
    },
    Suffix {
        opd: VdSynExprIdx,
        opr: VdSynSuffixOpr,
    },
    SeparatedList {
        separator_class: VdSeparatorClass,
        items: VdSynExprIdxRange,
        // Spaces are not included here.
        // For example, for `xyz` the separators are empty.
        separators: SmallVec<[VdSynSeparator; 4]>,
    },
    LxDelimited {
        left_delimiter_token_idx: LxMathTokenIdx,
        left_delimiter: LxMathDelimiter,
        item: VdSynExprIdx,
        right_delimiter_token_idx: LxMathTokenIdx,
        right_delimiter: LxMathDelimiter,
    },
    Delimited {
        left_delimiter: VdSynLeftDelimiter,
        item: VdSynExprIdx,
        right_delimiter: VdSynRightDelimiter,
    },
    Attach {
        base: VdSynExprIdx,
        // INVARIANCE: at least one of these are some
        scripts: Vec<(LxScriptKind, VdSynExprIdx)>,
    },
    Fraction {
        command_token_idx: LxMathTokenIdx,
        numerator: VdSynExprIdx,
        denominator: VdSynExprIdx,
        denominator_rcurl_token_idx: LxMathTokenIdx,
    },
    Sqrt {
        // TODO: add field for the index or degree
        command_token_idx: LxMathTokenIdx,
        radicand: VdSynExprIdx,
        radicand_rcurl_token_idx: LxMathTokenIdx,
    },
    UniadicChain,
    VariadicChain,
    UniadicArray,
    VariadicArray,
    Err(VdSynExprError),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynPrefixOpr {
    Base(LxTokenIdxRange, VdBasePrefixOpr),
    Composite(VdSynExprIdx, VdCompositePrefixOpr),
}

impl VdSynPrefixOpr {
    pub fn expr(self) -> Option<VdSynExprIdx> {
        match self {
            VdSynPrefixOpr::Base(..) => None,
            VdSynPrefixOpr::Composite(expr, _) => Some(expr),
        }
    }

    pub(crate) fn precedence(self) -> VdPrecedence {
        match self {
            VdSynPrefixOpr::Base(_, opr) => opr.precedence(),
            VdSynPrefixOpr::Composite(_, opr) => opr.precedence(),
        }
    }

    pub(crate) fn show(self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match self {
            VdSynPrefixOpr::Base(_, opr) => opr.latex_code().to_string(),
            VdSynPrefixOpr::Composite(_, opr) => opr.latex_code().to_string(), // ad hoc
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynSuffixOpr {
    Base(LxTokenIdxRange, VdBaseSuffixOpr),
    Composite(VdSynExprIdx, VdCompositeSuffixOpr),
}

impl VdSynSuffixOpr {
    pub fn expr(self) -> Option<VdSynExprIdx> {
        match self {
            VdSynSuffixOpr::Base(..) => None,
            VdSynSuffixOpr::Composite(expr, _) => Some(expr),
        }
    }

    pub(crate) fn show(&self, arena: VdSynExprArenaRef) -> String {
        match *self {
            VdSynSuffixOpr::Base(_, opr) => opr.latex_code().to_string(),
            VdSynSuffixOpr::Composite(_, opr) => opr.latex_code().to_string(), // ad hoc
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynBinaryOpr {
    Base(LxTokenIdxRange, VdBaseBinaryOpr),
    Composite(VdSynExprIdx, VdCompositeBinaryOpr),
}

impl VdSynBinaryOpr {
    pub(crate) fn left_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdSynBinaryOpr::Base(_, opr) => opr.left_precedence_range(),
            VdSynBinaryOpr::Composite(_, opr) => opr.left_precedence_range(),
        }
    }

    pub(crate) fn precedence(self) -> visored_opr::precedence::VdPrecedence {
        match self {
            VdSynBinaryOpr::Base(_, opr) => opr.precedence(),
            VdSynBinaryOpr::Composite(_, opr) => opr.precedence(),
        }
    }

    pub fn expr(self) -> Option<VdSynExprIdx> {
        match self {
            VdSynBinaryOpr::Base(..) => None,
            VdSynBinaryOpr::Composite(expr, _) => Some(expr),
        }
    }
}

impl VdSynBinaryOpr {
    pub(crate) fn show(&self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match *self {
            VdSynBinaryOpr::Base(_, opr) => opr.latex_code().to_string(),
            VdSynBinaryOpr::Composite(_, opr) => opr.latex_code().to_string(), // ad hoc
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynSeparator {
    /// for space, the range is that of the next token
    Base(LxTokenIdxRange, VdBaseSeparator),
    Composite(VdSynExprIdx, VdSeparatorClass),
}

impl VdSynSeparator {
    pub(crate) fn show(&self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match *self {
            VdSynSeparator::Base(_, slf) => slf.latex_code().to_string(),
            VdSynSeparator::Composite(slf, _) => arena[slf].show(db, arena),
        }
    }

    pub(crate) fn class(self) -> VdSeparatorClass {
        match self {
            VdSynSeparator::Base(_, separator) => separator.class(),
            VdSynSeparator::Composite(_, separator_class) => separator_class,
        }
    }

    pub(crate) fn left_precedence_range(self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynLeftDelimiter {
    Base(LxTokenIdxRange, VdBaseLeftDelimiter),
    Composite(VdSynExprIdx, VdCompositeLeftDelimiter),
}

impl VdSynLeftDelimiter {
    pub(crate) fn show(self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match self {
            VdSynLeftDelimiter::Base(token_idx_range, left_delimiter) => {
                left_delimiter.latex_code().to_string()
            }
            VdSynLeftDelimiter::Composite(expr, _) => arena[expr].show(db, arena),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynRightDelimiter {
    Base(LxTokenIdxRange, VdBaseRightDelimiter),
    Composite(VdSynExprIdx, VdCompositeRightDelimiter),
}

impl VdSynRightDelimiter {
    pub(crate) fn show(self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match self {
            VdSynRightDelimiter::Base(_, right_delimiter) => {
                right_delimiter.latex_code().to_string()
            }
            VdSynRightDelimiter::Composite(expr, _) => arena[expr].show(db, arena),
        }
    }
}

pub type VdSynExprIdx = ArenaIdx<VdSynExprData>;
pub type VdSynExprIdxRange = ArenaIdxRange<VdSynExprData>;
pub type VdSynExprArena = Arena<VdSynExprData>;
pub type VdSynExprMap<T> = ArenaMap<VdSynExprData, T>;
pub type VdSynExprOrderedMap<T> = ArenaOrderedMap<VdSynExprData, T>;
pub type VdSynExprArenaRef<'a> = ArenaRef<'a, VdSynExprData>;

impl VdSynExprData {
    pub fn children(&self) -> Vec<VdSynExprIdx> {
        match *self {
            VdSynExprData::Literal { .. }
            | VdSynExprData::Letter { .. }
            | VdSynExprData::BaseOpr { .. } => vec![],
            VdSynExprData::Binary { lopd, opr, ropd } => match opr {
                VdSynBinaryOpr::Base(_, _) => vec![lopd, ropd],
                VdSynBinaryOpr::Composite(opr, _) => vec![lopd, opr, ropd],
            },
            VdSynExprData::Prefix { opr, opd } => match opr {
                VdSynPrefixOpr::Base(_, _) => vec![opd],
                VdSynPrefixOpr::Composite(opr, _) => vec![opr, opd],
            },
            VdSynExprData::Suffix { opd, opr } => match opr {
                VdSynSuffixOpr::Base(_, _) => vec![opd],
                VdSynSuffixOpr::Composite(opr, _) => vec![opd, opr],
            },
            VdSynExprData::Attach { base, ref scripts } => [base]
                .into_iter()
                .chain(scripts.iter().map(|&(_, script)| script))
                .collect(),
            // ad hoc
            VdSynExprData::UniadicChain => vec![],
            // ad hoc
            VdSynExprData::VariadicChain => vec![],
            // ad hoc
            VdSynExprData::UniadicArray => vec![],
            // ad hoc
            VdSynExprData::VariadicArray => vec![],
            VdSynExprData::Err(..) => vec![],
            VdSynExprData::SeparatedList {
                items,
                ref separators,
                ..
            } => {
                let mut children = vec![];
                for (i, item) in items.into_iter().enumerate() {
                    children.push(item);
                    if i < separators.len() {
                        match separators[i] {
                            VdSynSeparator::Base(..) => (),
                            VdSynSeparator::Composite(separator, _) => children.push(separator),
                        }
                    }
                }
                children
            }
            VdSynExprData::LxDelimited { item, .. } => vec![item],
            VdSynExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => {
                let mut children = vec![];
                match left_delimiter {
                    VdSynLeftDelimiter::Base(_, _) => (),
                    VdSynLeftDelimiter::Composite(expr, _) => children.push(expr),
                }
                children.push(item);
                match right_delimiter {
                    VdSynRightDelimiter::Base(_, _) => (),
                    VdSynRightDelimiter::Composite(expr, _) => children.push(expr),
                }
                children
            }
            VdSynExprData::Fraction {
                numerator,
                denominator,
                ..
            } => vec![numerator, denominator],
            VdSynExprData::Sqrt { radicand, .. } => vec![radicand],
        }
    }

    pub fn class(&self) -> VdSynExprClass {
        match *self {
            VdSynExprData::Literal { .. }
            | VdSynExprData::Letter { .. }
            | VdSynExprData::LxDelimited { .. }
            | VdSynExprData::Delimited { .. }
            | VdSynExprData::Fraction { .. }
            | VdSynExprData::Sqrt { .. } => VdSynExprClass::Complete(VdPrecedence::ATOM),
            VdSynExprData::BaseOpr { opr } => match opr {
                VdBaseOpr::Prefix(opr) => VdSynExprClass::PrefixOpr,
                VdBaseOpr::Suffix(opr) => VdSynExprClass::SuffixOpr,
                VdBaseOpr::Binary(opr) => VdSynExprClass::BinaryOpr,
            },
            VdSynExprData::Binary { opr, .. } => VdSynExprClass::Complete(opr.precedence()),
            VdSynExprData::Prefix { opr, .. } => VdSynExprClass::Complete(opr.precedence()),
            VdSynExprData::Suffix { .. } => todo!(),
            VdSynExprData::Attach { .. } => todo!(),
            VdSynExprData::UniadicChain => todo!(),
            VdSynExprData::VariadicChain => todo!(),
            VdSynExprData::UniadicArray => todo!(),
            VdSynExprData::VariadicArray => todo!(),
            VdSynExprData::Err(..) => todo!(),
            VdSynExprData::SeparatedList {
                separator_class, ..
            } => VdSynExprClass::Complete(separator_class.precedence()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynExprClass {
    Complete(VdPrecedence),
    PrefixOpr,
    SuffixOpr,
    BinaryOpr,
    Separator,
}

impl VdSynExprClass {
    pub const ATOM: Self = VdSynExprClass::Complete(VdPrecedence::ATOM);
}

// token idx range is needed because the ast idx range might be empty,
// in which case we need to return an error yet can't determine the token idx range from the ast idx range alone
impl ToVdSyn<VdSynExprIdx> for (LxTokenIdxRange, LxMathAstIdxRange) {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynExprIdx {
        let (token_range, asts) = self;
        if asts.is_empty() {
            builder.alloc_expr(VdSynExprData::Err(
                OriginalVdSynExprError::Empty(token_range).into(),
            ))
        } else {
            let parser = builder.parser();
            parser.parse_asts(asts)
        }
    }
}

impl ToVdSyn<VdSynExprIdx> for LxMathAstIdx {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynExprIdx {
        let token_idx_range = builder.ast_token_idx_range_map()[self];
        (token_idx_range, LxMathAstIdxRange::new_single(self)).to_vd_syn(builder)
    }
}

impl VdSynExprData {
    pub fn show(&self, db: &::salsa::Db, arena: VdSynExprArenaRef) -> String {
        match *self {
            VdSynExprData::Literal {
                token_idx_range,
                literal,
            } => match literal.data(db) {
                VdZfcLiteralData::NaturalNumber(n) => n.to_string(),
                VdZfcLiteralData::NegativeInteger(n) => n.to_string(),
                VdZfcLiteralData::FiniteDecimalRepresentation(n) => n.to_string(),
                VdZfcLiteralData::SpecialConstant(vd_zfc_special_constant) => todo!(),
            },
            VdSynExprData::Letter { letter, .. } => letter.latex_code().to_string(),
            VdSynExprData::BaseOpr { opr } => opr.latex_code().to_string(),
            VdSynExprData::Binary { lopd, opr, ropd } => {
                format!(
                    "{} {} {}",
                    arena[lopd].show(db, arena),
                    opr.show(db, arena),
                    arena[ropd].show(db, arena)
                )
            }
            VdSynExprData::Prefix { opr, opd } => todo!(),
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::SeparatedList {
                items,
                ref separators,
                ..
            } => {
                let mut result = String::new();
                for (i, item) in items.into_iter().enumerate() {
                    if i > 0 && i - 1 < separators.len() {
                        result.push_str(" ");
                        result.push_str(&separators[i - 1].show(db, arena));
                        result.push_str(" ");
                    }
                    result.push_str(&arena[item].show(db, arena));
                }
                result
            }
            VdSynExprData::Attach { base, ref scripts } => todo!(),
            VdSynExprData::LxDelimited {
                left_delimiter,
                item,
                right_delimiter,
                ..
            } => format!(
                "{}{}{}",
                left_delimiter.left_latex_code(),
                arena[item].show(db, arena),
                right_delimiter.right_latex_code()
            ),
            VdSynExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => format!(
                "{}{}{}",
                left_delimiter.show(db, arena),
                arena[item].show(db, arena),
                right_delimiter.show(db, arena)
            ),
            VdSynExprData::Fraction {
                numerator,
                denominator,
                ..
            } => format!(
                "\\frac{{{}}}{{{}}}",
                arena[numerator].show(db, arena),
                arena[denominator].show(db, arena)
            ),
            VdSynExprData::Sqrt { radicand, .. } => {
                format!("\\sqrt{{{}}}", arena[radicand].show(db, arena))
            }
            VdSynExprData::UniadicChain => todo!(),
            VdSynExprData::VariadicChain => todo!(),
            VdSynExprData::UniadicArray => todo!(),
            VdSynExprData::VariadicArray => todo!(),
            VdSynExprData::Err(ref error) => error.to_string(),
        }
    }
}

impl<'db> VdSynSymbolBuilder<'db> {
    pub(crate) fn build_expr_aux(
        &mut self,
        expr: VdSynExprIdx,
    ) -> VdSynSymbolResolutionResult<Option<VdSynSymbolResolutions>> {
        for expr in self.expr_arena()[expr].children() {
            self.build_expr(expr);
        }
        match self.expr_arena()[expr] {
            VdSynExprData::Letter {
                token_idx_range,
                letter,
            } => self.build_letter(token_idx_range, letter).map(Some),
            VdSynExprData::BaseOpr { opr } => todo!(),
            _ => Ok(None),
        }
    }
}
