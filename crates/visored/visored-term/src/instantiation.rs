pub mod menu;

use crate::term::VdTerm;
use lisp_csv::expr::LpCsvExpr;
use smallvec::SmallVec;
use visored_entity_path::path::VdItemPath;

#[interned::interned]
pub struct VdInstantiation {
    pub path: VdItemPath,
    pub arguments: SmallVec<[VdTerm; 4]>,
}

impl std::fmt::Debug for VdInstantiation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ...", self.path())
    }
}

impl VdInstantiation {
    pub fn from_lp_csv_expr(expr: &LpCsvExpr) -> Self {
        let (path, args) = expr.application_expansion();
        let path = VdItemPath::from_lp_csv_expr(path);
        let arguments = args
            .iter()
            .map(|arg| VdTerm::from_lp_csv_expr(arg))
            .collect();
        Self::new(path, arguments)
    }
}
