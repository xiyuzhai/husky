pub mod text;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum FigureZone {
    Gallery = 1,
    Text,
}

impl FigureZone {
    pub fn len(self) -> usize {
        match self {
            FigureZone::Gallery => 1,
            FigureZone::Text => 1,
        }
    }
}
