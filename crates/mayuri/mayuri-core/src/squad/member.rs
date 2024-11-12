use crate::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx};

#[derive(Debug)]
pub enum MayuriSquadMemberData {
    Local,
    Remote,
}

pub type MayuriSquadMemberIdx = ArenaIdx<MayuriSquadMemberData>;
pub type MayuriSquadMemberArena = Arena<MayuriSquadMemberData>;
pub type MayuriSquadMemberMap<V> = ArenaMap<MayuriSquadMemberData, V>;
