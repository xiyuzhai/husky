pub mod hypothesis;
pub mod obvious;

pub trait HasHeader {
    fn header(&self) -> &'static str;
}
