use super::*;
use husky_hir_lazy_expr::{
    helpers::hir_lazy_expr_source_map_from_syn, variable::HirLazyVariableIdx, HirLazyExprIdx,
    HirLazyStmtIdx,
};
use husky_regional_token::RegionalTokenIdxRange;
use husky_sem_expr::{helpers::range::sem_expr_range_region, SemExprDb};
use husky_syn_defn::{item_syn_defn, ItemSynDefn};
use salsa::DebugWithDb;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KiReprSource {
    Val(MajorFormPath),
    Expansion {
        parent_ki_repr: KiRepr,
        source: KiReprExpansionSource,
    },
}

impl KiReprSource {
    pub fn debug_info(self, db: &::salsa::Db) -> String {
        // ad hoc
        let extra = match self {
            KiReprSource::Val(_) => "".to_string(),
            KiReprSource::Expansion {
                parent_ki_repr,
                source,
            } => format!(
                r#"regional_token_idx_range = {:?}"#,
                self.regional_token_idx_range(db)
            ),
        };
        format!(
            r#"self = {:?},
{extra}"#,
            self.debug(db)
        )
    }

    pub fn regional_token_idx_range(self, db: &::salsa::Db) -> RegionalTokenIdxRange {
        match self {
            KiReprSource::Val(_) => todo!(),
            KiReprSource::Expansion {
                parent_ki_repr,
                source,
            } => match parent_ki_repr.opn(db) {
                KiOpn::Require => todo!(),
                KiOpn::Assert => todo!(),
                KiOpn::Val(path) => {
                    let ItemSynDefn {
                        syn_expr_region, ..
                    } = item_syn_defn(db, path.into()).unwrap();
                    let sem_expr_region = db.sem_expr_region(syn_expr_region);
                    let sem_expr_range_region_data =
                        sem_expr_range_region(db, sem_expr_region).data(db);
                    let source_map_data =
                        hir_lazy_expr_source_map_from_syn(syn_expr_region, db).data(db);
                    match source {
                        KiReprExpansionSource::LetVariable { stmt, variable_idx } => todo!(),
                        KiReprExpansionSource::RequireDefault { stmt } => todo!(),
                        KiReprExpansionSource::RequireCondition { stmt } => todo!(),
                        KiReprExpansionSource::AssertCondition { stmt } => todo!(),
                        KiReprExpansionSource::IfCondition { stmt } => todo!(),
                        KiReprExpansionSource::ElifCondition { stmt, branch_idx } => todo!(),
                        KiReprExpansionSource::Expr { expr } => {
                            sem_expr_range_region_data
                                [source_map_data.hir_lazy_to_sem_expr_idx(expr).unwrap()]
                        }
                        KiReprExpansionSource::Stmt { stmt } => todo!(),
                    }
                }
                KiOpn::FunctionRitchie(_) => todo!(),
                KiOpn::Linket(linket) => todo!(),
                _ => unreachable!(),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KiReprExpansionSource {
    LetVariable {
        stmt: HirLazyStmtIdx,
        variable_idx: HirLazyVariableIdx,
    },
    RequireDefault {
        stmt: HirLazyStmtIdx,
    },
    RequireCondition {
        stmt: HirLazyStmtIdx,
    },
    AssertCondition {
        stmt: HirLazyStmtIdx,
    },
    IfCondition {
        stmt: HirLazyStmtIdx,
    },
    ElifCondition {
        stmt: HirLazyStmtIdx,
        branch_idx: u8,
    },
    Expr {
        expr: HirLazyExprIdx,
    },
    Stmt {
        stmt: HirLazyStmtIdx,
    },
}

impl KiReprSource {
    pub(crate) fn caching_class(self) -> KiCachingClass {
        match self {
            KiReprSource::Val(_) => KiCachingClass::Val,
            KiReprSource::Expansion { source, .. } => source.caching_class(),
        }
    }
}

impl KiReprExpansionSource {
    pub(crate) fn caching_class(self) -> KiCachingClass {
        match self {
            KiReprExpansionSource::LetVariable { .. } => KiCachingClass::Variable,
            KiReprExpansionSource::RequireDefault { .. } => KiCachingClass::Expr,
            KiReprExpansionSource::RequireCondition { .. }
            | KiReprExpansionSource::AssertCondition { .. }
            | KiReprExpansionSource::IfCondition { .. }
            | KiReprExpansionSource::ElifCondition { .. } => KiCachingClass::Condition,
            KiReprExpansionSource::Expr { .. } => KiCachingClass::Expr,
            KiReprExpansionSource::Stmt { .. } => KiCachingClass::Stmt,
        }
    }
}
