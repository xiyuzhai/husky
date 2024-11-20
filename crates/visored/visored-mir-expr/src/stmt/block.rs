use super::*;
use latex_environment::path::LxEnvironmentPath;
use visored_prelude::division::VdDivisionLevel;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirBlockMeta {
    Paragraph,
    Sentence,
    Environment(LxEnvironmentPath, VdModulePath),
    Division(VdDivisionLevel, VdModulePath),
}
