use crate::LnItemPath;
use lazy_static::lazy_static;

#[derive(Debug, PartialEq, Eq)]
pub struct LnItemPathMenu {
    pub nat: LnItemPath,
    pub rat: LnItemPath,
    pub int: LnItemPath,
    pub real: LnItemPath,
    pub complex: LnItemPath,
    pub ring_add: LnItemPath,
    pub ring_mul: LnItemPath,
    pub ring_pos: LnItemPath,
    pub ring_neg: LnItemPath,
    pub field_div: LnItemPath,
    pub le: LnItemPath,
    pub ge: LnItemPath,
    pub eq: LnItemPath,
    pub real_sqrt: LnItemPath,
}

impl LnItemPathMenu {
    pub fn new() -> Self {
        Self {
            nat: LnItemPath::NAT,
            rat: LnItemPath::RAT,
            int: LnItemPath::INT,
            real: LnItemPath::REAL,
            complex: LnItemPath::COMPLEX,
            ring_add: LnItemPath::RING_ADD,
            ring_mul: LnItemPath::RING_MUL,
            ring_pos: LnItemPath::RING_POS,
            ring_neg: LnItemPath::RING_NEG,
            field_div: LnItemPath::FIELD_DIV,
            le: LnItemPath::LE,
            ge: LnItemPath::GE,
            eq: LnItemPath::EQ,
            real_sqrt: LnItemPath::REAL_SQRT,
        }
    }
}

lazy_static! {
    pub static ref ln_item_path_menu: LnItemPathMenu = LnItemPathMenu::new();
}
