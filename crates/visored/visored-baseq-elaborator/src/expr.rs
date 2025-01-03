mod helpers;

use floated_sequential::{db::FloaterDb, floated};
use latex_math_letter::letter::LxMathLetter;
use smallvec::SmallVec;
use visored_entity_path::path::VdItemPath;
use visored_mir_expr::{
    expr::{
        application::VdMirFunc, VdMirExprArena, VdMirExprArenaRef, VdMirExprData, VdMirExprEntry,
        VdMirExprIdxRange, VdMirExprMap, VdMirExprOrderedMap,
    },
    region::VdMirExprRegionDataRef,
    symbol::local_defn::{
        storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead, VdMirSymbolLocalDefnIdx,
    },
};
use visored_opr::{
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::VdBaseSeparator,
};
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;
use visored_term::{
    term::literal::{VdLiteral, VdLiteralData},
    ty::VdType,
};

use crate::{session::VdBaseqSession, term::VdMirTermFld};

#[floated]
pub struct VdMirExprFld<'sess> {
    #[return_ref]
    pub data: VdMirExprFldData<'sess>,
    pub ty: VdType,
}

impl<'sess> std::fmt::Debug for VdMirExprFld<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdMirExprFld(`")?;
        self.show(VdPrecedenceRange::ANY, f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdMirExprFld<'sess> {
    pub fn show(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        if precedence_range.contains(self.data().outer_precedence()) {
            self.show_inner(f)
        } else {
            f.write_str("(")?;
            self.show_inner(f)?;
            f.write_str(")")
        }
    }

    fn show_inner(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.data() {
            VdMirExprFldData::Literal(literal) => literal.show(f),
            VdMirExprFldData::Variable(letter, _) => letter.show(f),
            VdMirExprFldData::Application {
                function,
                arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(vd_base_prefix_opr_signature) => todo!(),
                VdMirFunc::NormalBaseSeparator(vd_base_separator_signature) => todo!(),
                VdMirFunc::NormalBaseBinaryOpr(vd_base_binary_opr_signature) => todo!(),
                VdMirFunc::Power(vd_power_signature) => {
                    match arguments[1].data() {
                        VdMirExprFldData::Literal(literal) => match *literal.data() {
                            VdLiteralData::Nat128(n) if n < 10 => {
                                use husky_unicode_symbols::superscript::superscript;

                                // use unicode to show the superscript
                                let superscript = superscript(n as u8).unwrap();
                                arguments[0].show(VdPrecedenceRange::ATOM, f)?;
                                write!(f, "{}", superscript)?;
                                return Ok(());
                            }
                            _ => (),
                        },
                        _ => (),
                    }
                    todo!()
                }
                VdMirFunc::InSet => todo!(),
                VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => todo!(),
                VdMirFunc::NormalBaseFrac(vd_base_binary_opr_signature) => todo!(),
            },
            VdMirExprFldData::FoldingSeparatedList { leader, followers } => todo!(),
            VdMirExprFldData::ChainingSeparatedList {
                leader,
                followers,
                joined_separator_and_signature,
            } => {
                let VdMirFunc::NormalBaseSeparator(signature) = followers.first().unwrap().0 else {
                    todo!("maybe non base separator?")
                };
                let precedence_range = signature.opr().left_precedence_range();
                leader.show(precedence_range, f)?;
                for (func, follower) in followers {
                    let VdMirFunc::NormalBaseSeparator(signature) = func else {
                        todo!("maybe non base separator?")
                    };
                    f.write_str(" ")?;
                    signature.opr().show(f)?;
                    f.write_str(" ")?;
                    follower.show(precedence_range, f)?;
                }
                Ok(())
            }
            VdMirExprFldData::ItemPath(vd_item_path) => todo!(),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdMirExprFldData<'sess> {
    Literal(VdLiteral),
    Variable(LxMathLetter, VdMirSymbolLocalDefnIdx),
    Application {
        function: VdMirFunc,
        arguments: VdMirExprFlds<'sess>,
    },
    FoldingSeparatedList {
        leader: VdMirExprFld<'sess>,
        /// TODO: should we use VdBaseSeparatorSignature instead?
        followers: SmallVec<[(VdMirFunc, VdMirExprFld<'sess>); 4]>,
    },
    ChainingSeparatedList {
        leader: VdMirExprFld<'sess>,
        followers: SmallVec<[(VdMirFunc, VdMirExprFld<'sess>); 4]>,
        joined_separator_and_signature: Option<(VdBaseSeparator, VdBaseSeparatorSignature)>,
    },
    ItemPath(VdItemPath),
}

impl<'sess> VdMirExprFldData<'sess> {
    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdMirExprFldData::Literal(_) => VdPrecedence::ATOM,
            VdMirExprFldData::Variable(_, _) => VdPrecedence::ATOM,
            VdMirExprFldData::Application { function, .. } => function.outer_precedence(),
            VdMirExprFldData::FoldingSeparatedList { leader, followers } => todo!(),
            VdMirExprFldData::ChainingSeparatedList {
                leader,
                followers,
                joined_separator_and_signature,
            } => followers.first().unwrap().0.outer_precedence(),
            VdMirExprFldData::ItemPath(vd_item_path) => todo!(),
        }
    }
}

pub type VdMirExprFlds<'sess> = SmallVec<[VdMirExprFld<'sess>; 4]>;

impl<'sess> VdMirExprFld<'sess> {
    pub fn term(self, db: &'sess FloaterDb) -> VdMirTermFld<'sess> {
        // TODO: implement
        &()
    }
}

pub fn build_expr_to_fld_map<'db, 'sess>(
    session: &'sess VdBaseqSession<'db>,
    region_data: VdMirExprRegionDataRef,
) -> VdMirExprOrderedMap<VdMirExprFld<'sess>> {
    let mut map = VdMirExprOrderedMap::<VdMirExprFld<'sess>>::default();
    for (idx, entry) in region_data.expr_arena.indexed_iter() {
        let expr_fld = build_expr_to_fld_map_step(
            session.floater_db(),
            entry,
            &map,
            region_data.symbol_local_defn_storage,
        );
        map.insert_next(idx, expr_fld);
    }
    map
}

fn build_expr_to_fld_map_step<'sess>(
    db: &'sess FloaterDb,
    entry: &VdMirExprEntry,
    map: &VdMirExprOrderedMap<VdMirExprFld<'sess>>,
    symbol_local_defn_storage: &VdMirSymbolLocalDefnStorage,
) -> VdMirExprFld<'sess> {
    let data = match *entry.data() {
        VdMirExprData::Literal(vd_literal) => VdMirExprFldData::Literal(vd_literal),
        VdMirExprData::Variable(local_defn_idx) => {
            let lx_math_letter =
                match *symbol_local_defn_storage.defn_arena()[local_defn_idx].head() {
                    VdMirSymbolLocalDefnHead::Letter(lx_math_letter) => lx_math_letter,
                };
            VdMirExprFldData::Variable(lx_math_letter, local_defn_idx)
        }
        VdMirExprData::Application {
            function,
            arguments,
        } => VdMirExprFldData::Application {
            function,
            arguments: arguments.into_iter().map(|arg| map[arg]).collect(),
        },
        VdMirExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => VdMirExprFldData::FoldingSeparatedList {
            leader: map[leader],
            followers: followers
                .iter()
                .map(|&(func, follower)| (func, map[follower]))
                .collect(),
        },
        VdMirExprData::ChainingSeparatedList {
            leader,
            ref followers,
            joined_separator_and_signature,
        } => VdMirExprFldData::ChainingSeparatedList {
            leader: map[leader],
            followers: followers
                .iter()
                .map(|&(func, follower)| (func, map[follower]))
                .collect(),
            joined_separator_and_signature,
        },
        VdMirExprData::ItemPath(vd_item_path) => VdMirExprFldData::ItemPath(vd_item_path),
    };
    let ty = entry.ty();
    VdMirExprFld::new(data, ty, db)
}
