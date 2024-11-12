pub mod member;

use self::member::{
    MayuriSquadMemberArena, MayuriSquadMemberData, MayuriSquadMemberIdx, MayuriSquadMemberMap,
};

pub struct MayuriSquad {
    members: MayuriSquadMemberArena,
    progresses: MayuriSquadMemberMap<()>,
}

impl MayuriSquad {
    fn register(&mut self, data: MayuriSquadMemberData) -> MayuriSquadMemberIdx {
        self.members.alloc_one(data)
    }
}
