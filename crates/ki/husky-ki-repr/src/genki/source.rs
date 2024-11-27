use super::*;
use husky_entity_path::path::major_item::form::MajorFormPath;
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
pub enum GenkiReprSource {
    Val(MajorFormPath),
    Expansion {
        parent_ki_repr: GenkiRepr,
        source: GenkiReprExpansionSource,
    },
}

impl GenkiReprSource {
    pub fn debug_info(self, db: &::salsa::Db) -> String {
        // ad hoc
        let extra = match self {
            GenkiReprSource::Val(_) => "".to_string(),
            GenkiReprSource::Expansion {
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
            GenkiReprSource::Val(_) => todo!(),
            GenkiReprSource::Expansion {
                parent_ki_repr,
                source,
            } => match parent_ki_repr.opn(db) {
                GenkiOpn::Require => todo!(),
                GenkiOpn::Assert => todo!(),
                GenkiOpn::Val(path) => {
                    let ItemSynDefn {
                        syn_expr_region, ..
                    } = item_syn_defn(db, path.into()).unwrap();
                    let sem_expr_region = db.sem_expr_region(syn_expr_region);
                    let sem_expr_range_region_data =
                        sem_expr_range_region(db, sem_expr_region).data(db);
                    let source_map_data =
                        hir_lazy_expr_source_map_from_syn(syn_expr_region, db).data(db);
                    match source {
                        GenkiReprExpansionSource::LetVariable { stmt, variable_idx } => todo!(),
                        GenkiReprExpansionSource::RequireDefault { stmt } => todo!(),
                        GenkiReprExpansionSource::RequireCondition { stmt } => todo!(),
                        GenkiReprExpansionSource::AssertCondition { stmt } => todo!(),
                        GenkiReprExpansionSource::IfCondition { stmt } => todo!(),
                        GenkiReprExpansionSource::ElifCondition { stmt, branch_idx } => todo!(),
                        GenkiReprExpansionSource::Expr { expr } => {
                            sem_expr_range_region_data
                                [source_map_data.hir_lazy_to_sem_expr_idx(expr).unwrap()]
                        }
                        GenkiReprExpansionSource::Stmt { stmt } => todo!(),
                    }
                }
                GenkiOpn::FunctionRitchie(_) => todo!(),
                GenkiOpn::Linket(linket) => todo!(),
                _ => unreachable!(),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenkiReprExpansionSource {
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

impl GenkiReprSource {
    pub(crate) fn caching_class(self) -> KiCachingClass {
        match self {
            GenkiReprSource::Val(_) => KiCachingClass::Val,
            GenkiReprSource::Expansion { source, .. } => source.caching_class(),
        }
    }
}

impl GenkiReprExpansionSource {
    pub(crate) fn caching_class(self) -> KiCachingClass {
        match self {
            GenkiReprExpansionSource::LetVariable { .. } => KiCachingClass::Variable,
            GenkiReprExpansionSource::RequireDefault { .. } => KiCachingClass::Expr,
            GenkiReprExpansionSource::RequireCondition { .. }
            | GenkiReprExpansionSource::AssertCondition { .. }
            | GenkiReprExpansionSource::IfCondition { .. }
            | GenkiReprExpansionSource::ElifCondition { .. } => KiCachingClass::Condition,
            GenkiReprExpansionSource::Expr { .. } => KiCachingClass::Expr,
            GenkiReprExpansionSource::Stmt { .. } => KiCachingClass::Stmt,
        }
    }
}
