use std::sync::Arc;

use crate::tactic::VdBsqTactic;
use crate::*;
use config::VdBsqElaboratorConfig;
use floated_sequential::db::FloaterDb;
use strategy::obvious::load_obvious_tactics;
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_mir_expr::expr::VdMirExprIdx;

type SuperVarsContext = ();
type Term = ();

pub struct VdBsqSession<'db> {
    eterner_db: &'db EternerDb,
    dispatch_table: Arc<VdDefaultGlobalDispatchTable>,
    floater_db: FloaterDb,
    obvious_tactics: Vec<VdBsqTactic>,
    config: VdBsqElaboratorConfig,
}

impl<'db> VdBsqSession<'db> {
    pub fn new(
        eterner_db: &'db EternerDb,
        dispatch_table: Arc<VdDefaultGlobalDispatchTable>,
    ) -> Self {
        Self {
            eterner_db,
            dispatch_table,
            floater_db: FloaterDb::default(),
            obvious_tactics: load_obvious_tactics(),
            config: VdBsqElaboratorConfig::new_ad_hoc(),
        }
    }
}

impl<'db> VdBsqSession<'db> {
    pub fn eterner_db(&self) -> &'db EternerDb {
        self.eterner_db
    }

    pub fn floater_db(&self) -> &FloaterDb {
        &self.floater_db
    }

    pub fn dispatch_table(&self) -> &VdDefaultGlobalDispatchTable {
        &self.dispatch_table
    }

    pub fn obvious_tactics(&self) -> &[VdBsqTactic] {
        &self.obvious_tactics
    }

    pub fn config(&self) -> &VdBsqElaboratorConfig {
        &self.config
    }
}
