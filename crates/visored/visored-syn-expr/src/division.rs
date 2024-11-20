#[cfg(test)]
mod tests;

use std::iter::Peekable;

use crate::{
    builder::{ToVdSyn, VdSynExprBuilder},
    stmt::{VdSynStmtIdx, VdSynStmtIdxRange},
    *,
};
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_ast::ast::{
    root::{LxRootAstData, LxRootAstIdxRange},
    rose::{
        complete_command::{LxRoseCompleteCommandArgument, LxRoseCompleteCommandArgumentData},
        LxRoseAstData, LxRoseAstIdx, LxRoseAstIdxRange,
    },
    LxAstIdxRange,
};
use latex_token::idx::{LxRoseTokenIdx, LxTokenIdxRange};
use smallvec::{smallvec, SmallVec};
use visored_global_resolution::resolution::{
    command::VdCompleteCommandGlobalResolution, environment::VdEnvironmentGlobalResolution,
};
use visored_prelude::division::{VdDivisionLevel, VdDivisionLevelRange};

#[derive(Debug, PartialEq, Eq)]
pub enum VdSynDivisionData {
    Stmts {
        stmts: VdSynStmtIdxRange,
    },
    Divisions {
        command_token_idx: LxRoseTokenIdx,
        level: VdDivisionLevel,
        lcurl_token_idx: LxRoseTokenIdx,
        rcurl_token_idx: LxRoseTokenIdx,
        subdivisions: VdSynDivisionIdxRange,
    },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynDivisionChild {
    Division(VdSynDivisionIdx),
    Stmt(VdSynStmtIdx),
    Title(VdSynStmtIdxRange),
}

impl VdSynDivisionData {
    pub fn kind(&self) -> VdDivisionLevel {
        match *self {
            VdSynDivisionData::Stmts { .. } => VdDivisionLevel::Stmts,
            VdSynDivisionData::Divisions { level: kind, .. } => kind,
        }
    }

    pub fn children(&self) -> Vec<VdSynDivisionChild> {
        match *self {
            VdSynDivisionData::Stmts { stmts } => stmts
                .into_iter()
                .map(|stmt| VdSynDivisionChild::Stmt(stmt))
                .collect(),
            VdSynDivisionData::Divisions {
                subdivisions: divisions,
                ..
            } => divisions
                .into_iter()
                .map(|division| VdSynDivisionChild::Division(division))
                .collect(),
        }
    }
}

pub type VdSynDivisionArena = Arena<VdSynDivisionData>;
pub type VdSynDivisionArenaRef<'a> = ArenaRef<'a, VdSynDivisionData>;
pub type VdSynDivisionMap<T> = ArenaMap<VdSynDivisionData, T>;
pub type VdSynDivisionIdx = ArenaIdx<VdSynDivisionData>;
pub type VdSynDivisionIdxRange = ArenaIdxRange<VdSynDivisionData>;

impl ToVdSyn<VdSynDivisionIdxRange> for (LxTokenIdxRange, LxRootAstIdxRange) {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynDivisionIdxRange {
        self.1.to_vd_syn(builder)
        // let (_, ast_idx_range) = self;
        // builder.parse_stmts(ast_idx_range)
    }
}

impl ToVdSyn<VdSynDivisionIdxRange> for LxRootAstIdxRange {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynDivisionIdxRange {
        let (begin_rcurl_token_idx, asts, end_command_token_idx) = self
            .into_iter()
            .find_map(|root_ast| match builder.ast_arena().root()[root_ast] {
                LxRootAstData::Environment {
                    begin_command_token_idx,
                    begin_lcurl_token_idx,
                    begin_environment_name_token_idx,
                    begin_rcurl_token_idx,
                    asts,
                    end_command_token_idx,
                    end_lcurl_token_idx,
                    end_environment_name_token_idx,
                    end_rcurl_token_idx,
                    environment_signature,
                } if let Some(VdEnvironmentGlobalResolution::DOCUMENT) = builder
                    .default_resolution_table()
                    .resolve_environment(environment_signature.path()) =>
                {
                    match asts {
                        LxAstIdxRange::Rose(asts) => {
                            Some((begin_rcurl_token_idx, asts, end_command_token_idx))
                        }
                        _ => unreachable!(),
                    }
                }
                _ => None,
            })
            .unwrap();
        (
            LxTokenIdxRange::new(*begin_rcurl_token_idx + 1, *end_command_token_idx),
            asts,
        )
            .to_vd_syn(builder)
    }
}

impl ToVdSyn<VdSynDivisionIdxRange> for (LxTokenIdxRange, LxRoseAstIdxRange) {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> VdSynDivisionIdxRange {
        let (token_range, asts) = self;
        let mut ast_iter = asts.into_iter().peekable();
        let mut divisions = vec![];
        while let Some(division) = builder.build_division(&mut ast_iter, VdDivisionLevelRange::ANY)
        {
            divisions.push(division);
        }
        builder.alloc_divisions(divisions)
    }
}

impl<'a> VdSynExprBuilder<'a> {
    fn build_divisions(
        &mut self,
        ast_iter: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
        division_level_range: VdDivisionLevelRange,
    ) -> VdSynDivisionIdxRange {
        let mut divisions = vec![];
        while let Some(division) = self.build_division(ast_iter, division_level_range) {
            divisions.push(division);
        }
        self.alloc_divisions(divisions)
    }

    fn build_division(
        &mut self,
        ast_iter: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
        division_level_range: VdDivisionLevelRange,
    ) -> Option<VdSynDivisionData> {
        let ast_arena = self.ast_arena();
        let ast = *ast_iter.peek()?;
        match ast_arena[ast] {
            LxRoseAstData::CompleteCommand {
                command_token_idx,
                command_path,
                options,
                ref arguments,
            } if let Some(VdCompleteCommandGlobalResolution::NewDivision(level)) = self
                .default_resolution_table()
                .resolve_complete_command(command_path) =>
            {
                if division_level_range.contains(level) {
                    let _ = ast_iter.next().unwrap();
                    let &[argument] = &**arguments as &[LxRoseCompleteCommandArgument] else {
                        unreachable!()
                    };
                    let lcurl_token_idx = argument.lcurl_token_idx();
                    let LxRoseCompleteCommandArgumentData::Rose(title_asts) = argument.data()
                    else {
                        unreachable!()
                    };
                    let title = title_asts.to_vd_syn(self);
                    let rcurl_token_idx = argument.rcurl_token_idx();
                    let subdivisions =
                        self.build_divisions(ast_iter, VdDivisionLevelRange::Below(level));
                    Some(VdSynDivisionData::Divisions {
                        command_token_idx,
                        level,
                        lcurl_token_idx,
                        rcurl_token_idx,
                        subdivisions,
                    })
                } else {
                    None
                }
            }
            _ => Some(VdSynDivisionData::Stmts {
                stmts: self.build_stmt_aux(ast_iter),
            }),
        }
    }
}
