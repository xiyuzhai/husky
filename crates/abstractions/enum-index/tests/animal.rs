use enum_index::*;
use full_map::EnumFullVecMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, IsEnumIndex)]
pub enum Animal {
    Dog,
    Cat,
    Turtle,
    Bat,
    Penguin,
}

#[test]
fn animal_is_enum_index_works() {
    assert_eq!(Animal::Dog.index(), 0);
    assert_eq!(Animal::Dog, Animal::from_index(0));
    assert_eq!(Animal::Cat.index(), 1);
    assert_eq!(Animal::Cat, Animal::from_index(1));
    assert_eq!(Animal::Turtle.index(), 2);
    assert_eq!(Animal::Turtle, Animal::from_index(2));
    assert_eq!(Animal::Bat.index(), 3);
    assert_eq!(Animal::Bat, Animal::from_index(3));
    assert_eq!(Animal::Penguin.index(), 4);
    assert_eq!(Animal::Penguin, Animal::from_index(4));
}

type AnimalMap<T> = EnumFullVecMap<Animal, T>;

#[test]
fn animal_map_works() {
    let map = AnimalMap::<&str>::new(|animal| match animal {
        Animal::Dog => "dog",
        Animal::Cat => "cat",
        Animal::Turtle => "turtle",
        Animal::Bat => "bat",
        Animal::Penguin => "penguin",
    });
    assert_eq!(map[Animal::Dog], "dog");
    assert_eq!(map[Animal::Cat], "cat");
    assert_eq!(map[Animal::Turtle], "turtle");
    assert_eq!(map[Animal::Bat], "bat");
    assert_eq!(map[Animal::Penguin], "penguin");
}
