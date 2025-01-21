use super::*;
use crate::{
    expr::application::VdMirFunc, helpers::show::lisp_show_expr::VdMirExprLispShowExprBuilder,
};
use lisp_show_expr::LispShowExpr;
use visored_mir_opr::opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr};
use visored_mir_opr::separator::{
    chaining::VdMirBaseChainingSeparator, folding::VdMirBaseFoldingSeparator,
};

#[macro_use]
macro_rules! ds {
    (let (sqrt $radicand: ident) = $merge: expr, $hc: expr) => {
        let $radicand = $hc.split_sqrt($merge);
    };
    (let ($lopd: ident + $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_folding_separated_list(
            $merge,
            visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator::COMM_RING_ADD,
        );
    };
    (let ($lopd: ident * $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_folding_separated_list(
            $merge,
            visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator::COMM_RING_MUL,
        );
    };
    (let ($lopd: ident ** $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_pow($merge);
    };
    (let ($lopd: ident ^ $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_pow($merge);
    };
    (let ($lopd: ident = $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_trivial_chaining_separated_list(
            $merge,
            visored_mir_opr::separator::chaining::VdMirBaseChainingSeparator::EQ,
        );
    };
    (let ($lopd: ident => $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_term_reduction($merge);
    };
    (let ($lopd: ident - $ropd: ident) = $merge: expr, $hc: expr) => {
        let ($lopd, $ropd) = $hc.split_binary(
            $merge,
            visored_mir_opr::opr::binary::VdMirBaseBinaryOpr::CommRingSub,
        );
    };
    (let (-$opd: ident) = $merge: expr, $hc: expr) => {
        let $opd = $hc.split_prefix(
            $merge,
            visored_mir_opr::opr::prefix::VdMirBasePrefixOpr::RING_NEG,
        );
    };
}

pub(crate) use ds;
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;
use visored_term::term::VdTerm;

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn mk_expr(&mut self, entry: VdMirExprEntry) -> VdMirExprIdx {
        self.expr_arena.alloc_one(entry)
    }

    pub fn mk_zero(&mut self, expected_ty: Option<VdType>) -> VdMirExprIdx {
        let db = self.db;
        self.expr_arena.alloc_one(VdMirExprEntry::new(
            VdMirExprData::Literal(VdLiteral::new_int128(0, db)),
            self.ty_menu.nat,
            expected_ty,
        ))
    }

    pub fn mk_exprs(
        &mut self,
        exprs: impl IntoIterator<Item = VdMirExprEntry>,
    ) -> VdMirExprIdxRange {
        self.expr_arena.alloc_many(exprs)
    }

    pub fn mk_sub(
        &mut self,
        lhs: VdMirExprIdx,
        rhs: VdMirExprIdx,
        expected_ty: Option<VdType>,
    ) -> VdMirExprIdx {
        todo!()
    }

    #[track_caller]
    pub fn split_folding_separated_list(
        &mut self,
        lhs: VdMirExprIdx,
        separator: VdMirBaseFoldingSeparator,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        match *self.expr_arena[lhs].data() {
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                for (signature, _) in followers {
                    assert_eq!(separator, signature.separator());
                }
                match followers.len() {
                    0 => unreachable!(),
                    1 => (leader, followers[0].1),
                    _ => todo!(),
                }
            }
            _ => unreachable!("{:?}", self.expr_arena[lhs].data()),
        }
    }

    #[track_caller]
    pub fn split_trivial_chaining_separated_list(
        &mut self,
        expr: VdMirExprIdx,
        separator: VdMirBaseChainingSeparator,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        match *self.expr_arena[expr].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: None,
            } => {
                for (signature, _) in followers {
                    assert_eq!(separator, signature.separator());
                }
                match followers.len() {
                    0 => unreachable!(),
                    1 => (leader, followers[0].1),
                    _ => todo!(),
                }
            }
            _ => unreachable!(
                "try to split non-separated list: `{:?}` with lisp form: `{}`",
                self.expr_arena[expr].data(),
                self.show_expr_lisp(expr)
            ),
        }
    }

    #[track_caller]
    pub fn split_any_trivial_chaining_separated_list(
        &mut self,
        expr: VdMirExprIdx,
    ) -> (VdMirExprIdx, VdBaseChainingSeparatorSignature, VdMirExprIdx) {
        match *self.expr_arena[expr].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: None,
            } => match followers.len() {
                0 => unreachable!(),
                1 => (leader, followers[0].0, followers[0].1),
                _ => todo!(),
            },
            _ => unreachable!(
                "try to split non-separated list: `{:?}` with lisp form: `{}`",
                self.expr_arena[expr].data(),
                self.show_expr_lisp(expr)
            ),
        }
    }

    #[track_caller]
    pub fn split_any_trivial_chaining_separated_list_with_signature_checked(
        &mut self,
        expr: VdMirExprIdx,
        f: impl Fn(&Self, VdMirExprIdx, VdBaseChainingSeparatorSignature) -> bool,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        match *self.expr_arena[expr].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: None,
            } => {
                assert_eq!(followers.len(), 1);
                let (signature, follower) = followers[0];
                assert!(f(self, leader, signature));
                (leader, follower)
            }
            _ => unreachable!(
                "try to split non-separated list: `{:?}` with lisp form: `{}`",
                self.expr_arena[expr].data(),
                self.show_expr_lisp(expr)
            ),
        }
    }

    #[track_caller]
    pub fn split_term_reduction(&mut self, expr: VdMirExprIdx) -> (VdMirExprIdx, VdMirExprIdx) {
        self.split_any_trivial_chaining_separated_list_with_signature_checked(
            expr,
            |slf, leader, signature| {
                let ty = slf.expr_arena[leader].ty();
                let expected_separator = if ty == slf.ty_menu.prop {
                    VdMirBaseChainingSeparator::IFF
                } else {
                    VdMirBaseChainingSeparator::EQ
                };
                signature.separator() == expected_separator
            },
        )
    }

    #[track_caller]
    pub fn split_binary(
        &mut self,
        expr: VdMirExprIdx,
        opr: VdMirBaseBinaryOpr,
    ) -> (VdMirExprIdx, VdMirExprIdx) {
        let VdMirExprData::Application {
            function,
            arguments,
        } = *self.expr_arena[expr].data()
        else {
            unreachable!("{:?}", self.expr_arena[expr].data())
        };
        let VdMirFunc::NormalBaseBinaryOpr(signature) = function else {
            unreachable!()
        };
        assert_eq!(signature.opr(), opr);
        assert_eq!(arguments.len(), 2);
        (arguments.first().unwrap(), arguments.last().unwrap())
    }

    #[track_caller]
    pub fn split_sqrt(&mut self, expr: VdMirExprIdx) -> VdMirExprIdx {
        let VdMirExprData::Application {
            function,
            arguments,
        } = *self.expr_arena[expr].data()
        else {
            unreachable!("{:?}", self.expr_arena[expr].data())
        };
        let VdMirFunc::NormalBaseSqrt(signature) = function else {
            unreachable!()
        };
        assert_eq!(arguments.len(), 1);
        arguments.first().unwrap()
    }

    #[track_caller]
    pub fn split_prefix(&mut self, expr: VdMirExprIdx, opr: VdMirBasePrefixOpr) -> VdMirExprIdx {
        let VdMirExprData::Application {
            function,
            arguments,
        } = *self.expr_arena[expr].data()
        else {
            unreachable!("{:?}", self.expr_arena[expr].data())
        };
        let VdMirFunc::NormalBasePrefixOpr(signature) = function else {
            unreachable!()
        };
        assert_eq!(signature.opr(), opr);
        assert_eq!(arguments.len(), 1);
        arguments.first().unwrap()
    }

    #[track_caller]
    pub fn split_pow(&mut self, expr: VdMirExprIdx) -> (VdMirExprIdx, VdMirExprIdx) {
        let VdMirExprData::Application {
            function,
            arguments,
        } = *self.expr_arena[expr].data()
        else {
            unreachable!("{:?}", self.expr_arena[expr].data())
        };
        let VdMirFunc::Power(signature) = function else {
            unreachable!()
        };
        assert_eq!(arguments.len(), 2);
        (arguments.first().unwrap(), arguments.last().unwrap())
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn show_expr_lisp(&self, expr: VdMirExprIdx) -> LispShowExpr {
        let builder = VdMirExprLispShowExprBuilder::new(
            self.db,
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            &self.symbol_local_defn_storage,
        );
        builder.render_expr(expr)
    }
}
