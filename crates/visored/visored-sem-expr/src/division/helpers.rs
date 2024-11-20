use super::*;
use stmt::VdSemStmtIdx;

pub enum VdSemDivisionChild {
    Division(VdSemDivisionIdx),
    Title(VdSemStmtIdxRange),
    Stmt(VdSemStmtIdx),
}

impl VdSemDivisionData {
    pub(crate) fn children(&self) -> Vec<VdSemDivisionChild> {
        match *self {
            VdSemDivisionData::Stmts { stmts } => {
                stmts.into_iter().map(VdSemDivisionChild::Stmt).collect()
            }
            VdSemDivisionData::Divisions {
                command_token_idx,
                level,
                lcurl_token_idx,
                rcurl_token_idx,
                subdivisions,
            } => subdivisions
                .into_iter()
                .map(|division| VdSemDivisionChild::Division(division))
                .collect(),
        }
    }
}
