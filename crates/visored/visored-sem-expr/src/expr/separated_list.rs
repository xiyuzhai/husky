use super::*;
use smallvec::{smallvec, SmallVec};
use visored_global_dispatch::dispatch::separator::{
    join::VdBaseChainingSeparatorJoinDispatch, VdSeparatorGlobalDispatch,
};
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;
use visored_syn_expr::expr::VdSynExprIdxRange;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemSeparator {
    Base(LxTokenIdxRange, VdBaseSeparator),
    Composite(VdSemExprIdx, VdSeparatorClass),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdSemSeparatedListFollower {
    pub separator: VdSemSeparator,
    pub expr: VdSemExprIdx,
    pub dispatch: VdSemSeparatedListFollowerDispatch,
}

pub type VdSemSeparatedListFollowers = SmallVec<[VdSemSeparatedListFollower; 4]>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemSeparatedListFollowerDispatch {
    Folding {
        base_separator: VdBaseSeparator,
        signature: VdBaseSeparatorSignature,
    },
    Chaining {
        base_separator: VdBaseSeparator,
        signature: VdBaseSeparatorSignature,
    },
    InSet {
        expr_ty: VdType,
    },
}
impl VdSemSeparatedListFollowerDispatch {
    pub fn left_item_ty(&self, mut mk_ty_from_right_item_term: impl FnMut() -> VdType) -> VdType {
        match self {
            VdSemSeparatedListFollowerDispatch::Folding {
                base_separator,
                signature,
            } => signature.item_ty(),
            VdSemSeparatedListFollowerDispatch::Chaining {
                base_separator,
                signature,
            } => signature.item_ty(),
            VdSemSeparatedListFollowerDispatch::InSet { expr_ty, .. } => {
                mk_ty_from_right_item_term()
            }
        }
    }

    fn expr_ty(&self) -> VdType {
        match *self {
            VdSemSeparatedListFollowerDispatch::Folding {
                base_separator,
                ref signature,
            } => signature.expr_ty(),
            VdSemSeparatedListFollowerDispatch::Chaining {
                base_separator,
                ref signature,
            } => signature.expr_ty(),
            VdSemSeparatedListFollowerDispatch::InSet { expr_ty } => expr_ty,
        }
    }

    fn from_global(dispatch: VdSeparatorGlobalDispatch) -> VdSemSeparatedListFollowerDispatch {
        match dispatch {
            VdSeparatorGlobalDispatch::Folding {
                base_separator,
                signature,
            } => VdSemSeparatedListFollowerDispatch::Folding {
                base_separator,
                signature,
            },
            VdSeparatorGlobalDispatch::Chaining {
                base_separator,
                signature,
            } => VdSemSeparatedListFollowerDispatch::Chaining {
                base_separator,
                signature,
            },
            VdSeparatorGlobalDispatch::InSet { expr_ty } => {
                VdSemSeparatedListFollowerDispatch::InSet { expr_ty }
            }
        }
    }
}

impl<'db> VdSemExprBuilder<'db> {
    pub(super) fn build_separated_list(
        &mut self,
        separator_class: VdSeparatorClass,
        items: VdSynExprIdxRange,
        separators: &[VdSynSeparator],
    ) -> VdSemExprEntry {
        let (leader, followers) = match separator_class {
            VdSeparatorClass::Space => self.build_space_separated_list_aux(items, separators),
            _ => self.build_non_space_separated_list_aux(items, separators),
        };
        if followers.is_empty() {
            return leader;
        }
        let followers = self.calc_separated_list_dispatches(&leader, followers);
        let leader_expected_ty = followers[0]
            .dispatch
            .left_item_ty(|| VdType::new(self.infer_expr_term(followers[0].expr)));
        let leader = self.alloc_expr(items.first().unwrap(), leader, Some(leader_expected_ty));
        let ty = followers.last().unwrap().dispatch.expr_ty();
        let data = match separator_class {
            VdSeparatorClass::Relation => {
                let joined_separator_and_signature =
                    self.infer_joined_separator_and_signature(&followers);
                VdSemExprData::ChainingSeparatedList {
                    separator_class,
                    leader,
                    followers,
                    joined_separator_and_signature,
                }
            }
            VdSeparatorClass::Comma => todo!(),
            VdSeparatorClass::Semicolon => todo!(),
            VdSeparatorClass::Space | VdSeparatorClass::Mul | VdSeparatorClass::Add => {
                VdSemExprData::FoldingSeparatedList {
                    separator_class,
                    leader,
                    followers,
                }
            }
            VdSeparatorClass::Deduction => todo!(),
        };
        VdSemExprEntry::new(data, ty)
    }

    fn build_space_separated_list_aux(
        &mut self,
        items: VdSynExprIdxRange,
        separators: &[VdSynSeparator],
    ) -> (
        VdSemExprEntry,
        SmallVec<[(VdSemSeparator, VdSynExprIdx, VdSemExprEntry); 4]>,
    ) {
        let db = self.db();
        debug_assert_eq!(items.len(), separators.len() + 1);
        let mut item_iter = items.into_iter().enumerate();
        let mut t = || -> Option<(usize, VdSynExprIdx, VdSemExprEntry)> {
            let (i, syn_item) = item_iter.next()?;
            let mut item = self.build_expr_entry(syn_item);
            while item.ty.is_function_like(db) {
                todo!()
            }
            Some((i, syn_item, item))
        };
        let (_, _, fst) = t().unwrap();
        let mut others = smallvec![];
        while let Some((i, syn_item, item)) = t() {
            let separator = match separators[i - 1] {
                VdSynSeparator::Base(token_idx_range, VdBaseSeparator::Space) => {
                    VdSemSeparator::Base(token_idx_range, VdBaseSeparator::Space)
                }
                _ => unreachable!(),
            };
            others.push((separator, syn_item, item));
        }
        (fst, others)
    }

    fn build_non_space_separated_list_aux(
        &mut self,
        items: VdSynExprIdxRange,
        separators: &[VdSynSeparator],
    ) -> (
        VdSemExprEntry,
        SmallVec<[(VdSemSeparator, VdSynExprIdx, VdSemExprEntry); 4]>,
    ) {
        let mut item_iter = items.into_iter();
        let leader = self.build_expr_entry(item_iter.next().unwrap());
        let followers = separators
            .iter()
            .copied()
            .zip(item_iter)
            .map(|(sep, syn_item)| {
                let separator = sep.to_vd_sem(self);
                let expr_entry = self.build_expr_entry(syn_item);
                (separator, syn_item, expr_entry)
            })
            .collect();
        (leader, followers)
    }

    fn calc_separated_list_dispatches(
        &mut self,
        leader: &VdSemExprEntry,
        followers0: SmallVec<[(VdSemSeparator, VdSynExprIdx, VdSemExprEntry); 4]>,
    ) -> VdSemSeparatedListFollowers {
        let mut prev_item_ty = leader.ty();
        let mut followers: VdSemSeparatedListFollowers = smallvec![];
        for (separator, syn_expr, expr_entry) in followers0 {
            let dispatch =
                self.calc_separated_list_dispatch_step(prev_item_ty, separator, expr_entry.ty());
            prev_item_ty = expr_entry.ty();
            let expr = self.alloc_expr(
                syn_expr,
                expr_entry,
                Some(dispatch.right_item_ty(self.ty_menu())),
            );
            followers.push(VdSemSeparatedListFollower {
                separator,
                expr,
                dispatch: VdSemSeparatedListFollowerDispatch::from_global(dispatch),
            });
        }
        followers
    }

    fn calc_separated_list_dispatch_step(
        &mut self,
        prev_item_ty: VdType,
        separator: VdSemSeparator,
        next_item_ty: VdType,
    ) -> VdSeparatorGlobalDispatch {
        let base_separator = match separator {
            VdSemSeparator::Base(_, base_separator) => base_separator,
            VdSemSeparator::Composite(_, _) => todo!(),
        };
        if let Some(default_dispatch) = self
            .default_global_dispatch_table()
            .base_separator_default_dispatch(prev_item_ty, base_separator, next_item_ty)
        {
            return default_dispatch;
        }
        todo!(
            "no default dispatch for prev_item_ty = {:?}, separator = {:?}, next_item_ty = {:?}",
            prev_item_ty,
            separator,
            next_item_ty
        )
    }

    fn infer_joined_separator_and_signature(
        &mut self,
        followers: &VdSemSeparatedListFollowers,
    ) -> Option<(VdBaseSeparator, VdBaseSeparatorSignature)> {
        if followers.len() == 1 {
            return None;
        }
        let mut follower_iter = followers.iter().copied();
        let fst = follower_iter.next().unwrap();
        let VdSemSeparatedListFollowerDispatch::Chaining {
            base_separator,
            signature,
        } = fst.dispatch
        else {
            use husky_print_utils::*;
            p!(fst.dispatch, followers.len());
            unreachable!()
        };
        let mut opr = base_separator;
        let mut signature = signature;
        for follower in follower_iter {
            (opr, signature) =
                self.infer_joined_separator_and_signature_step(opr, signature, follower);
        }
        Some((opr, signature))
    }

    fn infer_joined_separator_and_signature_step(
        &mut self,
        cumulative_opr: VdBaseSeparator,
        cumulative_signature: VdBaseSeparatorSignature,
        next: VdSemSeparatedListFollower,
    ) -> (VdBaseSeparator, VdBaseSeparatorSignature) {
        let VdSemSeparatedListFollowerDispatch::Chaining {
            base_separator: next_base_separator,
            signature: next_signature,
        } = next.dispatch
        else {
            unreachable!()
        };
        if cumulative_signature == next_signature {
            debug_assert_eq!(cumulative_opr, next_base_separator);
            return (next_base_separator, next_signature);
        }
        let Some(dispatch) = self
            .default_global_dispatch_table()
            .base_chaining_separator_join_default_dispatch(cumulative_signature, next_signature)
        else {
            todo!(
                "cumulative signature = {:?}, next_signature = {:?}",
                cumulative_signature,
                next_signature
            )
        };
        match dispatch {
            VdBaseChainingSeparatorJoinDispatch::Ok {
                base_separator,
                signature,
            } => (base_separator, signature),
            VdBaseChainingSeparatorJoinDispatch::Err => todo!(),
        }
    }
}
