pub mod builder;
pub mod comnum;
pub mod litnum;
pub mod num;
pub mod prop;
pub mod set;

use self::{comnum::*, litnum::*, num::*, prop::*, set::*};
use crate::{
    elaborator::VdBsqElaboratorInner,
    expr::{VdBsqExprFld, VdBsqExprFldData},
    foundations::opr::separator::relation::comparison::VdBsqComparisonOpr,
    hypothesis::VdBsqHypothesisIdx,
};
use bigint::VdBsqBigInt;
use builder::{product::VdBsqProductBuilder, sum::VdBsqSumBuilder};
use either::*;
use floated_sequential::db::FloaterDb;
use floated_sequential::floated;
use frac128::VdBsqFrac128;
use num_chain::VdBsqNumChain;
use product::VdBsqProductStem;
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;
use visored_entity_path::path::VdItemPath;
use visored_mir_expr::{
    expr::{application::VdMirFunc, VdMirExprData, VdMirExprEntry, VdMirExprIdx},
    hypothesis::constructor::VdMirHypothesisConstructor,
    symbol::local_defn::{
        storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
    },
};
use visored_mir_opr::{
    opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr},
    separator::VdMirBaseSeparator,
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
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
    pub fn num(self) -> Option<VdBsqNumTerm<'sess>> {
        match self {
            VdBsqTerm::Litnum(litnum) => Some(VdBsqNumTerm::Litnum(litnum)),
            VdBsqTerm::Comnum(comnum) => Some(VdBsqNumTerm::Comnum(comnum)),
            VdBsqTerm::Prop(_) => None,
            VdBsqTerm::Set(_) => None,
        }
    }
}

impl<'sess> std::fmt::Debug for VdBsqTerm<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdBsqTerm(`")?;
        self.show_fmt(VdPrecedenceRange::Any, f)?;
        f.write_str("`)")
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
    pub fn calc_expr_term(&self, expr: &VdBsqExprFldData<'sess>, ty: VdType) -> VdBsqTerm<'sess> {
        let db = self.floater_db();
        match *expr {
            VdBsqExprFldData::Literal(vd_literal) => match *vd_literal.data() {
                VdLiteralData::Int128(i) => VdBsqTerm::Litnum(VdBsqLitnumTerm::Int128(i)),
                VdLiteralData::BigInt(ref n) => {
                    VdBsqTerm::Litnum(VdBsqLitnumTerm::BigInt(VdBsqBigInt::new(n.clone(), db)))
                }
                VdLiteralData::Float(_) => todo!(),
                VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
            },
            VdBsqExprFldData::Variable(lx_math_letter, local_defn_idx) => {
                if ty.is_numeric(self.eterner_db()) {
                    if let Some(_) = self.eval_variable() {
                        todo!()
                    } else {
                        VdBsqTerm::new_numeric_variable(
                            lx_math_letter,
                            local_defn_idx,
                            self.floater_db(),
                        )
                    }
                } else {
                    todo!()
                }
            }
            VdBsqExprFldData::Application {
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
                VdMirFunc::NormalBaseSeparator(signature) => todo!(),
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
                VdMirFunc::InSet => todo!(),
                VdMirFunc::NormalBaseSqrt(signature) => {
                    let radicand = arguments[0].term().num().unwrap();
                    let exponent = VdBsqFrac128::new128(1, 2).unwrap();
                    VdBsqTerm::new_power(radicand, exponent, self.floater_db())
                }
            },
            VdBsqExprFldData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                let (func, follower) = *followers.first().unwrap();
                let num_relationship = |slf: &Self, kind| {
                    VdBsqTerm::new_num_relationship(
                        leader.term().num().unwrap(),
                        kind,
                        follower.term().num().unwrap(),
                        self.floater_db(),
                    )
                };
                match func {
                    VdMirFunc::NormalBasePrefixOpr(signature) => todo!(),
                    VdMirFunc::NormalBaseSeparator(signature) => match signature.opr() {
                        VdMirBaseSeparator::CommRingAdd => {
                            let mut builder = VdBsqSumBuilder::new(self.floater_db());
                            builder.add_num(leader.term().num().unwrap());
                            for &(_, follower) in followers.iter() {
                                builder.add_num(follower.term().num().unwrap());
                            }
                            builder.finish().into()
                        }
                        VdMirBaseSeparator::CommRingMul => {
                            let mut builder = VdBsqProductBuilder::new(self.floater_db());
                            builder.mul_num(leader.term().num().unwrap());
                            for &(_, follower) in followers.iter() {
                                builder.mul_num(follower.term().num().unwrap());
                            }
                            builder.finish().into()
                        }
                        VdMirBaseSeparator::Eq => todo!(),
                        VdMirBaseSeparator::Ne => todo!(),
                        VdMirBaseSeparator::Lt => todo!(),
                        VdMirBaseSeparator::Gt => todo!(),
                        VdMirBaseSeparator::Le => todo!(),
                        VdMirBaseSeparator::Ge => todo!(),
                        VdMirBaseSeparator::Subset => todo!(),
                        VdMirBaseSeparator::Supset => todo!(),
                        VdMirBaseSeparator::Subseteq => todo!(),
                        VdMirBaseSeparator::Supseteq => todo!(),
                        VdMirBaseSeparator::Subseteqq => todo!(),
                        VdMirBaseSeparator::Supseteqq => todo!(),
                        VdMirBaseSeparator::Subsetneq => todo!(),
                        VdMirBaseSeparator::Supsetneq => todo!(),
                        VdMirBaseSeparator::In => todo!(),
                        VdMirBaseSeparator::Notin => todo!(),
                        VdMirBaseSeparator::SetTimes => todo!(),
                        VdMirBaseSeparator::TensorOtimes => todo!(),
                        VdMirBaseSeparator::Iff => todo!(),
                    },
                    VdMirFunc::NormalBaseBinaryOpr(signature) => todo!(),
                    VdMirFunc::Power(signature) => todo!(),
                    VdMirFunc::InSet => todo!(),
                    VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => todo!(),
                }
            }
            VdBsqExprFldData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: joined_separator_and_signature,
            } => match joined_separator_and_signature {
                Some(joined_separator_and_signature) => VdBsqNumChain::new(
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

                    let (func, follower) = *followers.first().unwrap();
                    let num_relationship = |slf: &Self, kind| {
                        VdBsqTerm::new_num_relationship(
                            leader.term().num().unwrap(),
                            kind,
                            follower.term().num().unwrap(),
                            self.floater_db(),
                        )
                    };
                    match func {
                        VdMirFunc::NormalBasePrefixOpr(signature) => todo!(),
                        VdMirFunc::NormalBaseSeparator(signature) => match signature.opr() {
                            VdMirBaseSeparator::CommRingAdd => todo!(),
                            VdMirBaseSeparator::CommRingMul => todo!(),
                            VdMirBaseSeparator::Eq => {
                                num_relationship(self, VdBsqComparisonOpr::EQ)
                            }
                            VdMirBaseSeparator::Ne => {
                                num_relationship(self, VdBsqComparisonOpr::NE)
                            }
                            VdMirBaseSeparator::Lt => {
                                num_relationship(self, VdBsqComparisonOpr::LT)
                            }
                            VdMirBaseSeparator::Gt => {
                                num_relationship(self, VdBsqComparisonOpr::GT)
                            }
                            VdMirBaseSeparator::Le => {
                                num_relationship(self, VdBsqComparisonOpr::LE)
                            }
                            VdMirBaseSeparator::Ge => {
                                num_relationship(self, VdBsqComparisonOpr::GE)
                            }
                            VdMirBaseSeparator::Subset => todo!(),
                            VdMirBaseSeparator::Supset => todo!(),
                            VdMirBaseSeparator::Subseteq => todo!(),
                            VdMirBaseSeparator::Supseteq => todo!(),
                            VdMirBaseSeparator::Subseteqq => todo!(),
                            VdMirBaseSeparator::Supseteqq => todo!(),
                            VdMirBaseSeparator::Subsetneq => todo!(),
                            VdMirBaseSeparator::Supsetneq => todo!(),
                            VdMirBaseSeparator::In => todo!(),
                            VdMirBaseSeparator::Notin => todo!(),
                            VdMirBaseSeparator::SetTimes => todo!(),
                            VdMirBaseSeparator::TensorOtimes => todo!(),
                            VdMirBaseSeparator::Iff => todo!(),
                        },
                        VdMirFunc::NormalBaseBinaryOpr(signature) => todo!(),
                        VdMirFunc::Power(signature) => todo!(),
                        VdMirFunc::InSet => VdBsqPropTerm::InSet.into(),
                        VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => todo!(),
                    }
                }
            },
            VdBsqExprFldData::ItemPath(path) => match path {
                VdItemPath::Category(path) => todo!(),
                VdItemPath::Set(path) => VdBsqSetTerm::Path(path).into(),
                VdItemPath::Function(path) => todo!(),
                VdItemPath::Trait(path) => todo!(),
                VdItemPath::TraitItem(path) => todo!(),
                VdItemPath::Prop(vd_prop_path) => todo!(),
            },
        }
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn transcribe_term(
        &self,
        term: VdBsqTerm<'sess>,
        expected_ty: Option<VdType>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprIdx {
        let (data, ty) = self.transcribe_term_data_and_ty(term, hypothesis_constructor);
        hypothesis_constructor.construct_expr(VdMirExprEntry::new(data, ty, expected_ty))
    }

    fn transcribe_term_data_and_ty(
        &self,
        term: VdBsqTerm<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        match term {
            VdBsqTerm::Litnum(litnum) => {
                self.transcribe_litnum_data_and_ty(litnum, hypothesis_constructor)
            }
            VdBsqTerm::Comnum(comnum) => {
                self.transcribe_comnum_data(comnum, hypothesis_constructor)
            }
            VdBsqTerm::Prop(prop) => self.transcribe_prop_data_and_ty(prop, hypothesis_constructor),
            VdBsqTerm::Set(set) => self.transcribe_set_data_and_ty(set, hypothesis_constructor),
        }
    }

    fn transcribe_litnum_data_and_ty(
        &self,
        litnum: VdBsqLitnumTerm<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        let db = self.eterner_db();
        match litnum {
            VdBsqLitnumTerm::Int128(i) => {
                if i >= 0 {
                    (
                        VdMirExprData::Literal(VdLiteral::new_int128(i, db)),
                        self.ty_menu().nat,
                    )
                } else {
                    (
                        VdMirExprData::Literal(VdLiteral::new_int128(i, db)),
                        self.ty_menu().int,
                    )
                }
            }
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(f) => {
                let a = VdMirExprData::Application {
                    function: VdMirFunc::NormalBaseBinaryOpr(self.signature_menu().rat_div),
                    arguments: hypothesis_constructor.construct_exprs([
                        VdMirExprEntry::new(
                            VdMirExprData::Literal(VdLiteral::new_int128(f.numerator(), db)),
                            if f.numerator() >= 0 {
                                self.ty_menu().nat
                            } else {
                                self.ty_menu().int
                            },
                            Some(self.ty_menu().rat),
                        ),
                        VdMirExprEntry::new(
                            VdMirExprData::Literal(VdLiteral::new_int128(f.denominator(), db)),
                            self.ty_menu().nat,
                            Some(self.ty_menu().rat),
                        ),
                    ]),
                };
                (a, self.ty_menu().rat)
            }
        }
    }

    fn transcribe_comnum_data(
        &self,
        comnum: VdBsqComnumTerm<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        todo!()
    }

    fn transcribe_set_data_and_ty(
        &self,
        set: VdBsqSetTerm<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        todo!()
    }
}
