#[cfg(feature = "egui")]
pub mod egui;

pub trait IsHotkeyBuffer {}

// Trivial implementation for the unit type ()
impl IsHotkeyBuffer for () {}
