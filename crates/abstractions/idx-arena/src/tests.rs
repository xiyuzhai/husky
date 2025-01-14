use crate::*;

#[test]
fn find_rev_indexed_works() {
    #[allow(dead_code)]
    struct Player(usize);

    type PlayerArena = Arena<Player>;

    let mut arena = PlayerArena::default();
    arena.alloc_many([Player(0), Player(0)]);
    assert_eq!(
        arena.find_rev_indexed(|_| true).map(|(i, _)| i.index()),
        Some(1)
    );
}
