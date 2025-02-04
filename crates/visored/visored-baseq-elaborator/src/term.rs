pub mod builder;
pub mod comnum;
pub mod litnum;
pub mod num;
pub mod prop;
pub mod set;

use self::{comnum::*, litnum::*, num::*, prop::*, set::*};
use crate::{
    elaborator::VdBsqElaboratorInner,
    expr::{VdBsqExpr, VdBsqExprData},
    foundations::opr::separator::relation::comparison::VdBsqComparisonOpr,
    hypothesis::VdBsqHypothesisIdx,
    *,
};
use bigint::VdBsqBigInt;
use builder::{product::VdBsqProductBuilder, sum::VdBsqSumBuilder};
use either::*;
use floated_sequential::db::FloaterDb;
use floated_sequential::floated;
use frac128::VdBsqFrac128;
use iff::VdBsqIff;
use in_set::VdBsqInSet;
use num_chain::VdBsqNumChain;
use product::VdBsqProductStem;
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;
use visored_entity_path::path::{prop::VdPropPath, VdItemPath};
use visored_mir_expr::{
    expr::{application::VdMirFunc, VdMirExprData, VdMirExprEntry, VdMirExprIdx},
    hypothesis::constructor::VdMirHypothesisConstructor,
    symbol::local_defn::{
        storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
    },
};
use visored_mir_opr::{
    opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr},
    separator::{
        chaining::VdMirBaseChainingSeparator, folding::VdMirBaseFoldingSeparator,
        VdMirBaseSeparator,
    },
};
use visored_opr::precedence::VdPrecedenceRange;
use visored_term::{
    term::{
        literal::{VdLiteral, VdLiteralData},
        VdTermData,
    },
    ty::VdType,
};

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqTerm<'sess> {
    Litnum(VdBsqLitnumTerm<'sess>),
    Comnum(VdBsqComnumTerm<'sess>),
    Prop(VdBsqPropTerm<'sess>),
    Set(VdBsqSetTerm<'sess>),
}

impl<'sess> VdBsqNumTerm<'sess> {
    pub fn product_or_non_product(
        self,
    ) -> Either<(VdBsqLitnumTerm<'sess>, VdBsqProductStem<'sess>), VdBsqNumTerm<'sess>> {
        match self {
            VdBsqNumTerm::Litnum(term) => todo!(),
            VdBsqNumTerm::Comnum(term) => match term {
                VdBsqComnumTerm::Atom(term) => Right(term.into()),
                VdBsqComnumTerm::Sum(term) => Right(term.into()),
                VdBsqComnumTerm::Product(product) => {
                    Left((product.litnum_factor(), product.stem()))
                }
            },
        }
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn trivial(self) -> Option<bool> {
        match self {
            VdBsqTerm::Prop(VdBsqPropTerm::Trivial(b)) => Some(b),
            _ => None,
        }
    }

    pub fn is_trivial(self) -> bool {
        self.trivial().is_some()
    }

    pub fn is_nontrivial(self) -> bool {
        !self.is_trivial()
    }

    pub fn num(self) -> Option<VdBsqNumTerm<'sess>> {
        match self {
            VdBsqTerm::Litnum(litnum) => Some(VdBsqNumTerm::Litnum(litnum)),
            VdBsqTerm::Comnum(comnum) => Some(VdBsqNumTerm::Comnum(comnum)),
            VdBsqTerm::Prop(_) => None,
            VdBsqTerm::Set(_) => None,
        }
    }

    pub fn prop(self) -> Option<VdBsqPropTerm<'sess>> {
        match self {
            VdBsqTerm::Prop(prop) => Some(prop),
            _ => None,
        }
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqTerm::Litnum(litnum) => litnum.show_fmt(precedence_range, f),
            VdBsqTerm::Comnum(comnum) => comnum.show_fmt(precedence_range, f),
            VdBsqTerm::Prop(prop) => prop.show_fmt(precedence_range, f),
            VdBsqTerm::Set(set) => set.show_fmt(precedence_range, f),
        }
    }
}

impl<'sess> std::fmt::Debug for VdBsqNumTerm<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdBsqNumTerm(`")?;
        self.show_fmt(VdPrecedenceRange::Any, f)?;
        f.write_str("`)")
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn calc_expr_term(&self, expr: &VdBsqExprData<'sess>, ty: VdType) -> VdBsqTerm<'sess> {
        let db = self.floater_db();
        match *expr {
            VdBsqExprData::Literal(vd_literal) => match *vd_literal.data() {
                VdLiteralData::Int(ref n) => VdBsqBigInt::new_or_i128_ref(n, db).into(),
                VdLiteralData::Frac(ref frac) => match VdBsqFrac128::from_vd_frac(frac) {
                    Some(frac) => VdBsqLitnumTerm::Frac128(frac).into(),
                    None => todo!(),
                },
            },
            VdBsqExprData::Variable(lx_math_letter, local_defn_idx) => {
                if ty.is_numeric(self.eterner_db()) {
                    if let Some(_) = self.eval_variable() {
                        todo!()
                    } else {
                        VdBsqTerm::new_numeric_variable(
                            lx_math_letter,
                            local_defn_idx,
                            ty,
                            self.floater_db(),
                        )
                    }
                } else {
                    todo!()
                }
            }
            VdBsqExprData::Application {
                function,
                ref arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(signature) => match signature.opr {
                    VdMirBasePrefixOpr::RingPos => arguments[0].term(),
                    VdMirBasePrefixOpr::RingNeg => arguments[0]
                        .term()
                        .num()
                        .unwrap()
                        .neg(self.floater_db())
                        .into(),
                    _ => todo!(),
                },
                VdMirFunc::NormalBaseSeparator(signature) => {
                    unreachable!("should be chaining or folding")
                }
                VdMirFunc::NormalBaseBinaryOpr(signature) => match signature.opr {
                    VdMirBaseBinaryOpr::CommRingSub => {
                        let lopd = arguments[0].term().num().unwrap();
                        let ropd = arguments[1].term().num().unwrap();
                        lopd.sub(ropd, self.floater_db()).into()
                    }
                    VdMirBaseBinaryOpr::CommFieldDiv => {
                        let lopd = arguments[0].term().num().unwrap();
                        let ropd = arguments[1].term().num().unwrap();
                        lopd.div(ropd, self.floater_db()).into()
                    }
                },
                VdMirFunc::Power(signature) => {
                    assert_eq!(arguments.len(), 2);
                    let Some(base) = arguments[0].term().num() else {
                        todo!()
                    };
                    let Some(exponent) = arguments[1].term().num() else {
                        todo!()
                    };
                    // TODO: simplify???
                    VdBsqTerm::new_power(base, exponent, self.floater_db())
                    // match base.product_or_non_product() {
                    //     Left(_) => todo!(),
                    //     Right(base) => VdBsqTerm::new_power(base, exponent, self.floater_db()),
                    // }
                }
                VdMirFunc::NormalBaseSqrt(signature) => {
                    let radicand = arguments[0].term().num().unwrap();
                    let exponent = VdBsqFrac128::new128(1, 2).unwrap();
                    VdBsqTerm::new_power(radicand, exponent, self.floater_db())
                }
            },
            VdBsqExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                let (signature, follower) = *followers.first().unwrap();
                let num_relationship = |slf: &Self, kind| {
                    VdBsqTerm::new_num_relationship(
                        leader.term().num().unwrap(),
                        kind,
                        follower.term().num().unwrap(),
                        self.floater_db(),
                    )
                };
                match signature.separator() {
                    VdMirBaseFoldingSeparator::CommRingAdd => {
                        let mut builder = VdBsqSumBuilder::new(self.floater_db());
                        builder.add_num(leader.term().num().unwrap());
                        for &(_, follower) in followers.iter() {
                            builder.add_num(follower.term().num().unwrap());
                        }
                        builder.finish().into()
                    }
                    VdMirBaseFoldingSeparator::CommRingMul => {
                        let mut builder = VdBsqProductBuilder::new(self.floater_db());
                        builder.mul_num(leader.term().num().unwrap());
                        for &(_, follower) in followers.iter() {
                            builder.mul_num(follower.term().num().unwrap());
                        }
                        builder.finish().into()
                    }
                    VdMirBaseFoldingSeparator::SetTimes => todo!(),
                    VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
                }
            }
            VdBsqExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: joined_chaining_separator_and_signature,
            } => match joined_chaining_separator_and_signature {
                Some(joined_chaining_separator_and_signature) => VdBsqNumChain::new(
                    leader.term().num().unwrap(),
                    followers
                        .iter()
                        .map(|&(func, follower)| (func, follower.term().num().unwrap()))
                        .collect(),
                    db,
                )
                .into(),
                None => {
                    use VdBsqComparisonOpr::*;

                    let (signature, follower) = *followers.first().unwrap();
                    let num_relationship = |slf: &Self, kind| {
                        VdBsqTerm::new_num_relationship(
                            leader.term().num().unwrap(),
                            kind,
                            follower.term().num().unwrap(),
                            self.floater_db(),
                        )
                    };
                    match signature.separator() {
                        VdMirBaseChainingSeparator::EQ => {
                            num_relationship(self, VdBsqComparisonOpr::EQ)
                        }
                        VdMirBaseChainingSeparator::NE => {
                            num_relationship(self, VdBsqComparisonOpr::NE)
                        }
                        VdMirBaseChainingSeparator::LT => {
                            num_relationship(self, VdBsqComparisonOpr::LT)
                        }
                        VdMirBaseChainingSeparator::GT => {
                            num_relationship(self, VdBsqComparisonOpr::GT)
                        }
                        VdMirBaseChainingSeparator::LE => {
                            num_relationship(self, VdBsqComparisonOpr::LE)
                        }
                        VdMirBaseChainingSeparator::GE => {
                            num_relationship(self, VdBsqComparisonOpr::GE)
                        }
                        VdMirBaseChainingSeparator::IN_SET => {
                            VdBsqInSet::new(leader.term(), follower.term(), self.floater_db())
                                .into()
                        }
                        VdMirBaseChainingSeparator::IFF => VdBsqIff::new(
                            leader.term().prop().unwrap(),
                            follower.term().prop().unwrap(),
                            self.floater_db(),
                        )
                        .into(),
                        separator => todo!("unsupported separator: {separator:?}"),
                    }
                }
            },
            VdBsqExprData::ItemPath(path) => match path {
                VdItemPath::Category(path) => todo!(),
                VdItemPath::Set(path) => VdBsqSetTerm::Path(path).into(),
                VdItemPath::Function(path) => todo!(),
                VdItemPath::Trait(path) => todo!(),
                VdItemPath::TraitItem(path) => todo!(),
                VdItemPath::Prop(path) => match path {
                    VdPropPath::True => VdBsqPropTerm::Trivial(true).into(),
                    VdPropPath::False => VdBsqPropTerm::Trivial(false).into(),
                },
            },
        }
    }
}

impl<'db, 'sess> VdBsqTerm<'sess> {
    pub fn expr(self, elr: &mut VdBsqElaboratorInner<'db, 'sess>) -> VdBsqExpr<'sess> {
        match self {
            VdBsqTerm::Litnum(litnum) => litnum.expr(elr),
            VdBsqTerm::Comnum(comnum) => comnum.expr(elr),
            VdBsqTerm::Prop(prop) => prop.expr(elr),
            VdBsqTerm::Set(set) => set.expr(elr),
        }
    }
}
