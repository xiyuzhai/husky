mod helpers;

use floated_sequential::{db::FloaterDb, floated};
use latex_math_letter::letter::LxMathLetter;
use smallvec::*;
use visored_entity_path::path::VdItemPath;
use visored_mir_expr::{
    expr::{
        application::VdMirFunc, VdMirExprArena, VdMirExprArenaRef, VdMirExprData, VdMirExprEntry,
        VdMirExprIdx, VdMirExprIdxRange, VdMirExprMap, VdMirExprOrderedMap,
    },
    hypothesis::constructor::VdMirHypothesisConstructor,
    region::VdMirExprRegionDataRef,
    symbol::local_defn::{
        storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
    },
};
use visored_mir_opr::{
    opr::prefix::VdMirBasePrefixOpr,
    separator::{folding::VdMirBaseFoldingSeparator, VdMirBaseSeparator},
};
use visored_opr::{
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::VdBaseSeparator,
};
use visored_signature::signature::{
    attach::VdPowerSignature,
    separator::base::{
        chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
        VdBaseSeparatorSignature,
    },
};
use visored_term::{
    term::literal::{VdLiteral, VdLiteralData},
    ty::VdType,
};

use crate::{
    elaborator::VdBsqElaboratorInner,
    hypothesis::VdBsqHypothesisIdx,
    session::VdBsqSession,
    term::{litnum::VdBsqLitnumTerm, VdBsqTerm},
};

#[floated]
pub struct VdBsqExpr<'sess> {
    #[return_ref]
    pub data: VdBsqExprData<'sess>,
    pub ty: VdType,
    pub term: VdBsqTerm<'sess>,
}

impl<'sess> std::fmt::Debug for VdBsqExpr<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdMirExprFld(`")?;
        self.show_fmt(VdPrecedenceRange::ANY, f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdBsqExpr<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        if precedence_range.contains(self.data().outer_precedence()) {
            self.show_fmt_inner(f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(f)?;
            f.write_str(")")
        }
    }

    fn show_fmt_inner(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.data() {
            VdBsqExprData::Literal(literal) => literal.show(f),
            VdBsqExprData::Variable(letter, _) => {
                write!(f, "{}", letter.unicode())
            }
            VdBsqExprData::Application {
                function,
                arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(signature) => match signature.opr {
                    VdMirBasePrefixOpr::RingPos => {
                        f.write_str("+")?;
                        arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)
                    }
                    VdMirBasePrefixOpr::RingNeg => {
                        f.write_str("-")?;
                        arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)
                    }
                    _ => todo!(),
                },
                VdMirFunc::NormalBaseSeparator(signature) => todo!(),
                VdMirFunc::NormalBaseBinaryOpr(signature) => {
                    let opr = signature.opr;
                    arguments[0].show_fmt(opr.left_precedence_range(), f)?;
                    f.write_str(" ")?;
                    f.write_str(opr.unicode())?;
                    f.write_str(" ")?;
                    arguments[1].show_fmt(opr.right_precedence_range(), f)?;
                    Ok(())
                }
                VdMirFunc::Power(signature) => {
                    use num_traits::cast::ToPrimitive;

                    match arguments[1].data() {
                        VdBsqExprData::Literal(literal) => match *literal.data() {
                            VdLiteralData::Int(ref i)
                                if let Some(i) = i.to_i128()
                                    && i >= 0
                                    && i < 10 =>
                            {
                                use husky_unicode_symbols::superscript::superscript;

                                // use unicode to show the superscript
                                let superscript = superscript(i as u8).unwrap();
                                arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)?;
                                write!(f, "{}", superscript)?;
                                return Ok(());
                            }
                            VdLiteralData::Frac(ref frac) if frac.is_frac128(1, 2) => {
                                f.write_str("√")?;
                                arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)?;
                                return Ok(());
                            }
                            _ => (),
                        },
                        _ => (),
                    }
                    arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)?;
                    write!(f, "^{{")?;
                    arguments[1].show_fmt(VdPrecedenceRange::ANY, f)?;
                    f.write_str("}}")
                }
                VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => {
                    f.write_str("√")?;
                    arguments[0].show_fmt(VdPrecedenceRange::ATOM, f)
                }
            },
            VdBsqExprData::FoldingSeparatedList { leader, followers } => {
                let signature = followers.first().unwrap().0;
                let precedence_range = signature.separator().left_precedence_range();
                leader.show_fmt(precedence_range, f)?;
                for (func, follower) in followers {
                    f.write_str(" ")?;
                    signature.separator().show_fmt(f)?;
                    f.write_str(" ")?;
                    follower.show_fmt(precedence_range, f)?;
                }
                Ok(())
            }
            VdBsqExprData::ChainingSeparatedList {
                leader,
                followers,
                joined_signature,
            } => {
                let signature = followers.first().unwrap().0;
                let precedence_range = signature.separator().left_precedence_range();
                leader.show_fmt(precedence_range, f)?;
                for (signature, follower) in followers {
                    f.write_str(" ")?;
                    signature.separator().show_fmt(f)?;
                    f.write_str(" ")?;
                    follower.show_fmt(precedence_range, f)?;
                }
                Ok(())
            }
            VdBsqExprData::ItemPath(path) => path.show_fmt(f),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqExprData<'sess> {
    Literal(VdLiteral),
    Variable(LxMathLetter, VdMirSymbolLocalDefnIdx),
    Application {
        function: VdMirFunc,
        arguments: VdMirExprFlds<'sess>,
    },
    FoldingSeparatedList {
        leader: VdBsqExpr<'sess>,
        /// TODO: should we use VdBaseSeparatorSignature instead?
        followers: SmallVec<[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>); 4]>,
    },
    ChainingSeparatedList {
        leader: VdBsqExpr<'sess>,
        followers: SmallVec<[(VdBaseChainingSeparatorSignature, VdBsqExpr<'sess>); 4]>,
        joined_signature: Option<VdBaseChainingSeparatorSignature>,
    },
    ItemPath(VdItemPath),
}

pub type VdBsqExprFoldingFollowers<'sess> =
    SmallVec<[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>); 4]>;
pub type VdBsqExprChainingFollowers<'sess> =
    SmallVec<[(VdBaseChainingSeparatorSignature, VdBsqExpr<'sess>); 4]>;

impl<'sess> VdBsqExprData<'sess> {
    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdBsqExprData::Literal(_) => VdPrecedence::ATOM,
            VdBsqExprData::Variable(_, _) => VdPrecedence::ATOM,
            VdBsqExprData::Application { function, .. } => function.outer_precedence(),
            VdBsqExprData::FoldingSeparatedList { leader, followers } => {
                followers[0].0.separator().outer_precedence()
            }
            VdBsqExprData::ChainingSeparatedList {
                leader,
                followers,
                joined_signature,
            } => followers.first().unwrap().0.separator().outer_precedence(),
            VdBsqExprData::ItemPath(vd_item_path) => VdPrecedence::ATOM,
        }
    }
}

pub type VdMirExprFlds<'sess> = SmallVec<[VdBsqExpr<'sess>; 4]>;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn cache_mir_expr_to_bsq(
        &mut self,
        expr_idx: VdMirExprIdx,
        region_data: VdMirExprRegionDataRef,
    ) {
        if self.mir_expr_to_bsq_map().has(expr_idx) {
            return;
        }
        let expr_entry = &region_data.expr_arena[expr_idx];
        let symbol_local_defn_storage = region_data.symbol_local_defn_storage;
        let expr_data = self.calc_expr_data(expr_entry, symbol_local_defn_storage);
        let ty = expr_entry.ty();
        let term = self.calc_expr_term(&expr_data, ty);
        let db = self.session().floater_db();
        let expr_fld = VdBsqExpr::new_inner(expr_data, ty, term, db);
        self.save_expr_fld(expr_idx, expr_fld);
    }

    fn calc_expr_data(
        &self,
        entry: &VdMirExprEntry,
        symbol_local_defn_storage: &VdMirSymbolLocalDefnStorage,
    ) -> VdBsqExprData<'sess> {
        match *entry.data() {
            VdMirExprData::Literal(vd_literal) => VdBsqExprData::Literal(vd_literal),
            VdMirExprData::Variable(local_defn_idx) => {
                let lx_math_letter =
                    match *symbol_local_defn_storage.defn_arena()[local_defn_idx].head() {
                        VdMirSymbolLocalDefnHead::Letter(lx_math_letter) => lx_math_letter,
                    };
                VdBsqExprData::Variable(lx_math_letter, local_defn_idx)
            }
            VdMirExprData::Application {
                function,
                arguments,
            } => VdBsqExprData::Application {
                function,
                arguments: arguments
                    .into_iter()
                    .map(|arg| self.expr_fld(arg))
                    .collect(),
            },
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => VdBsqExprData::FoldingSeparatedList {
                leader: self.expr_fld(leader),
                followers: followers
                    .iter()
                    .map(|&(func, follower)| (func, self.expr_fld(follower)))
                    .collect(),
            },
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => VdBsqExprData::ChainingSeparatedList {
                leader: self.expr_fld(leader),
                followers: followers
                    .iter()
                    .map(|&(func, follower)| (func, self.expr_fld(follower)))
                    .collect(),
                joined_signature,
            },
            VdMirExprData::ItemPath(vd_item_path) => VdBsqExprData::ItemPath(vd_item_path),
        }
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn mk_expr(&self, expr_data: VdBsqExprData<'sess>, ty: VdType) -> VdBsqExpr<'sess> {
        let term = self.calc_expr_term(&expr_data, ty);
        let db = self.session().floater_db();
        VdBsqExpr::new_inner(expr_data, ty, term, db)
    }

    pub(crate) fn mk_zero(&self) -> VdBsqExpr<'sess> {
        self.mk_expr(
            VdBsqExprData::Literal(self.term_menu().zero),
            self.ty_menu().nat,
        )
    }

    pub fn mk_i128(&self, i: i128) -> VdBsqExpr<'sess> {
        self.mk_litnum(VdBsqLitnumTerm::Int128(i))
    }

    pub(crate) fn mk_litnum(&self, litnum: VdBsqLitnumTerm<'sess>) -> VdBsqExpr<'sess> {
        let db = self.session().eterner_db();
        let ty_menu = self.ty_menu();
        let (lit, ty) = match litnum {
            VdBsqLitnumTerm::Int128(i) => (
                VdLiteral::new(VdLiteralData::Int(i.into()), db),
                if i >= 0 { ty_menu.nat } else { ty_menu.int },
            ),
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(frac128) => (
                VdLiteral::new_frac128(frac128.numerator(), frac128.denominator(), db),
                ty_menu.rat,
            ),
        };
        self.mk_expr(VdBsqExprData::Literal(lit), ty)
    }

    pub(crate) fn mk_literal(&self, literal: VdLiteral) -> VdBsqExpr<'sess> {
        self.mk_expr(
            VdBsqExprData::Literal(literal),
            literal.ty(self.eterner_db()),
        )
    }

    pub(crate) fn mk_eq(
        &self,
        lopd: VdBsqExpr<'sess>,
        ropd: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_eq_signature(lopd.ty(), ropd.ty());
        self.mk_expr(
            VdBsqExprData::ChainingSeparatedList {
                leader: lopd,
                followers: smallvec![(signature, ropd)],
                joined_signature: None,
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn mk_iff(
        &self,
        lopd: VdBsqExpr<'sess>,
        ropd: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_iff_signature(lopd.ty(), ropd.ty());
        self.mk_expr(
            VdBsqExprData::ChainingSeparatedList {
                leader: lopd,
                followers: smallvec![(signature, ropd)],
                joined_signature: None,
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn mk_add(
        &self,
        lopd: VdBsqExpr<'sess>,
        ropd: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_add_signature(lopd.ty(), ropd.ty());
        self.mk_expr(
            VdBsqExprData::FoldingSeparatedList {
                leader: lopd,
                followers: smallvec![(signature, ropd)],
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn mk_sub(
        &self,
        lhs: VdBsqExpr<'sess>,
        rhs: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_sub_signature(lhs.ty(), rhs.ty());
        self.mk_expr(
            VdBsqExprData::Application {
                function: VdMirFunc::NormalBaseBinaryOpr(signature),
                arguments: smallvec![lhs, rhs],
            },
            signature.expr_ty,
        )
    }

    pub(crate) fn mk_neg(
        &self,
        expr: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_neg_signature(expr.ty());
        self.mk_expr(
            VdBsqExprData::Application {
                function: VdMirFunc::NormalBasePrefixOpr(signature),
                arguments: smallvec![expr],
            },
            signature.expr_ty,
        )
    }

    pub(crate) fn mk_mul(
        &self,
        lopd: VdBsqExpr<'sess>,
        ropd: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_mul_signature(lopd.ty(), ropd.ty());
        self.mk_expr(
            VdBsqExprData::FoldingSeparatedList {
                leader: lopd,
                followers: smallvec![(signature, ropd)],
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn mk_div(
        &self,
        numerator: VdBsqExpr<'sess>,
        denominator: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_div_signature(numerator.ty(), denominator.ty());
        self.mk_expr(
            VdBsqExprData::Application {
                function: VdMirFunc::NormalBaseBinaryOpr(signature),
                arguments: smallvec![numerator, denominator],
            },
            signature.expr_ty,
        )
    }

    pub(crate) fn mk_pow(
        &self,
        base: VdBsqExpr<'sess>,
        exponent: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature = hc.infer_pow_signature(base.ty(), exponent.ty());
        self.mk_expr(
            VdBsqExprData::Application {
                function: VdMirFunc::Power(signature),
                arguments: smallvec![base, exponent],
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn mk_pow_one(
        &self,
        base: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        self.mk_pow(base, self.mk_litnum(VdBsqLitnumTerm::Int128(1)), hc)
    }

    pub(crate) fn mk_inv(
        &self,
        expr: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        self.mk_pow(expr, self.mk_litnum(VdBsqLitnumTerm::Int128(-1)), hc)
    }

    pub(crate) fn mk_trivial_chaining_separated_list(
        &self,
        leader: VdBsqExpr<'sess>,
        separator: VdBaseSeparator,
        follower: VdBsqExpr<'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let signature =
            hc.infer_base_chaining_separator_signature(leader.ty(), separator, follower.ty());
        self.mk_expr(
            VdBsqExprData::ChainingSeparatedList {
                leader,
                followers: smallvec![(signature, follower)],
                joined_signature: None,
            },
            signature.expr_ty(),
        )
    }

    pub(crate) fn split_folding_separated_list(
        &self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
    ) -> (
        VdBsqExpr<'sess>,
        VdBaseFoldingSeparatorSignature,
        VdBsqExpr<'sess>,
    ) {
        match followers.len() {
            0 => unreachable!(),
            1 => {
                let (signature, follower) = followers[0];
                (leader, signature, follower)
            }
            _ => {
                let last_signature = followers.last().unwrap().0;
                let lopd = self.mk_expr(
                    VdBsqExprData::FoldingSeparatedList {
                        leader,
                        followers: followers[..followers.len() - 1].to_smallvec(),
                    },
                    followers[followers.len() - 2].0.expr_ty(),
                );
                let signature = followers.last().unwrap().0;
                let ropd = followers.last().unwrap().1;
                (lopd, signature, ropd)
            }
        }
    }
}

impl<'db, 'sess> VdBsqExpr<'sess> {
    pub fn transcribe(
        &self,
        expected_ty: Option<VdType>,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprIdx {
        let entry = self.transcribe_entry(expected_ty, elr, hc);
        hc.mk_expr(entry)
    }

    pub fn transcribe_with_ty(
        &self,
        expected_ty: Option<VdType>,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprIdx, VdType) {
        let entry = self.transcribe_entry(expected_ty, elr, hc);
        let ty = entry.ty();
        (hc.mk_expr(entry), ty)
    }

    fn transcribe_entry(
        &self,
        expected_ty: Option<VdType>,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprEntry {
        let data = self.transcribe_expr_data(elr, hc);
        let ty = self.ty();
        VdMirExprEntry::new(data, ty, expected_ty)
    }

    fn transcribe_expr_data(
        &self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprData {
        match *self.data() {
            VdBsqExprData::Literal(lit) => VdMirExprData::Literal(lit),
            VdBsqExprData::Variable(_, symbol) => VdMirExprData::Variable(symbol),
            VdBsqExprData::Application {
                function,
                ref arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        arg.transcribe_entry(Some(function.argument_expected_ty(i)), elr, hc)
                    })
                    .collect::<Vec<_>>();
                VdMirExprData::Application {
                    function,
                    arguments: hc.mk_exprs(arguments),
                }
            }
            VdBsqExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => VdMirExprData::FoldingSeparatedList {
                leader: leader.transcribe(Some(followers[0].0.item_ty()), elr, hc),
                followers: followers
                    .iter()
                    .map(|&(func, follower)| {
                        (
                            func,
                            follower.transcribe(Some(followers[0].0.item_ty()), elr, hc),
                        )
                    })
                    .collect(),
            },
            VdBsqExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => VdMirExprData::ChainingSeparatedList {
                leader: leader.transcribe(Some(followers[0].0.left_item_ty()), elr, hc),
                followers: followers
                    .iter()
                    .map(|&(func, follower)| {
                        (
                            func,
                            follower.transcribe(Some(followers[0].0.right_item_ty()), elr, hc),
                        )
                    })
                    .collect(),
                joined_signature,
            },
            VdBsqExprData::ItemPath(path) => VdMirExprData::ItemPath(path),
        }
    }
}

impl<'db, 'sess> VdBsqExpr<'sess> {
    pub fn split_add(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (
        VdBsqExpr<'sess>,
        VdBaseFoldingSeparatorSignature,
        VdBsqExpr<'sess>,
    ) {
        self.split_folding_separated_list(VdMirBaseFoldingSeparator::COMM_RING_ADD, elr)
    }

    pub fn split_mul(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (
        VdBsqExpr<'sess>,
        VdBaseFoldingSeparatorSignature,
        VdBsqExpr<'sess>,
    ) {
        self.split_folding_separated_list(VdMirBaseFoldingSeparator::COMM_RING_MUL, elr)
    }

    #[track_caller]
    pub fn split_folding_separated_list(
        self,
        separator: VdMirBaseFoldingSeparator,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
    ) -> (
        VdBsqExpr<'sess>,
        VdBaseFoldingSeparatorSignature,
        VdBsqExpr<'sess>,
    ) {
        let VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } = *self.data()
        else {
            todo!()
        };

        assert!(followers[0].0.separator() == separator);

        if followers.len() == 1 {
            (leader, followers[0].0, followers[0].1)
        } else {
            let (signature, ropd) = *followers.last().unwrap();
            let lopd = elr.mk_expr(
                VdBsqExprData::FoldingSeparatedList {
                    leader,
                    followers: followers[..followers.len() - 1].to_smallvec(),
                },
                followers[followers.len() - 2].0.expr_ty(),
            );
            (lopd, signature, ropd)
        }
    }

    pub fn split_pow(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdBsqExpr<'sess>, VdPowerSignature, VdBsqExpr<'sess>) {
        let VdBsqExprData::Application {
            function: VdMirFunc::Power(signature),
            ref arguments,
        } = *self.data()
        else {
            todo!()
        };
        assert_eq!(arguments.len(), 2);
        let (base, exponent) = (arguments[0], arguments[1]);
        (base, signature, exponent)
    }

    pub fn split_trivial_chaining_separated_list(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (
        VdBsqExpr<'sess>,
        VdBaseChainingSeparatorSignature,
        VdBsqExpr<'sess>,
    ) {
        let VdBsqExprData::ChainingSeparatedList {
            leader,
            ref followers,
            joined_signature: None,
        } = *self.data()
        else {
            todo!()
        };
        assert_eq!(followers.len(), 1);
        let (signature, ropd) = followers[0];
        (leader, signature, ropd)
    }
}
