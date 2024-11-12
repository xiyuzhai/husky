use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxMathLatinLetter {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
    I,
    J,
    K,
    L,
    M,
    N,
    O,
    P,
    Q,
    R,
    S,
    T,
    U,
    V,
    W,
    X,
    Y,
    Z,
}

impl LxMathLatinLetter {
    pub fn upper_case_latex_code(self) -> &'static str {
        match self {
            LxMathLatinLetter::A => "A",
            LxMathLatinLetter::B => "B",
            LxMathLatinLetter::C => "C",
            LxMathLatinLetter::D => "D",
            LxMathLatinLetter::E => "E",
            LxMathLatinLetter::F => "F",
            LxMathLatinLetter::G => "G",
            LxMathLatinLetter::H => "H",
            LxMathLatinLetter::I => "I",
            LxMathLatinLetter::J => "J",
            LxMathLatinLetter::K => "K",
            LxMathLatinLetter::L => "L",
            LxMathLatinLetter::M => "M",
            LxMathLatinLetter::N => "N",
            LxMathLatinLetter::O => "O",
            LxMathLatinLetter::P => "P",
            LxMathLatinLetter::Q => "Q",
            LxMathLatinLetter::R => "R",
            LxMathLatinLetter::S => "S",
            LxMathLatinLetter::T => "T",
            LxMathLatinLetter::U => "U",
            LxMathLatinLetter::V => "V",
            LxMathLatinLetter::W => "W",
            LxMathLatinLetter::X => "X",
            LxMathLatinLetter::Y => "Y",
            LxMathLatinLetter::Z => "Z",
        }
    }

    pub fn lower_case_latex_code(self) -> &'static str {
        match self {
            LxMathLatinLetter::A => "a",
            LxMathLatinLetter::B => "b",
            LxMathLatinLetter::C => "c",
            LxMathLatinLetter::D => "d",
            LxMathLatinLetter::E => "e",
            LxMathLatinLetter::F => "f",
            LxMathLatinLetter::G => "g",
            LxMathLatinLetter::H => "h",
            LxMathLatinLetter::I => "i",
            LxMathLatinLetter::J => "j",
            LxMathLatinLetter::K => "k",
            LxMathLatinLetter::L => "l",
            LxMathLatinLetter::M => "m",
            LxMathLatinLetter::N => "n",
            LxMathLatinLetter::O => "o",
            LxMathLatinLetter::P => "p",
            LxMathLatinLetter::Q => "q",
            LxMathLatinLetter::R => "r",
            LxMathLatinLetter::S => "s",
            LxMathLatinLetter::T => "t",
            LxMathLatinLetter::U => "u",
            LxMathLatinLetter::V => "v",
            LxMathLatinLetter::W => "w",
            LxMathLatinLetter::X => "x",
            LxMathLatinLetter::Y => "y",
            LxMathLatinLetter::Z => "z",
        }
    }
}

impl LxMathLetter {
    pub const UPPER_A: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::A);
    pub const UPPER_B: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::B);
    pub const UPPER_C: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::C);
    pub const UPPER_D: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::D);
    pub const UPPER_E: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::E);
    pub const UPPER_F: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::F);
    pub const UPPER_G: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::G);
    pub const UPPER_H: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::H);
    pub const UPPER_I: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::I);
    pub const UPPER_J: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::J);
    pub const UPPER_K: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::K);
    pub const UPPER_L: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::L);
    pub const UPPER_M: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::M);
    pub const UPPER_N: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::N);
    pub const UPPER_O: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::O);
    pub const UPPER_P: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::P);
    pub const UPPER_Q: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::Q);
    pub const UPPER_R: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::R);
    pub const UPPER_S: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::S);
    pub const UPPER_T: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::T);
    pub const UPPER_U: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::U);
    pub const UPPER_V: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::V);
    pub const UPPER_W: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::W);
    pub const UPPER_X: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::X);
    pub const UPPER_Y: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::Y);
    pub const UPPER_Z: Self = LxMathLetter::UpperLatin(LxMathLatinLetter::Z);

    pub const LOWER_A: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::A);
    pub const LOWER_B: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::B);
    pub const LOWER_C: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::C);
    pub const LOWER_D: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::D);
    pub const LOWER_E: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::E);
    pub const LOWER_F: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::F);
    pub const LOWER_G: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::G);
    pub const LOWER_H: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::H);
    pub const LOWER_I: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::I);
    pub const LOWER_J: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::J);
    pub const LOWER_K: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::K);
    pub const LOWER_L: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::L);
    pub const LOWER_M: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::M);
    pub const LOWER_N: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::N);
    pub const LOWER_O: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::O);
    pub const LOWER_P: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::P);
    pub const LOWER_Q: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::Q);
    pub const LOWER_R: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::R);
    pub const LOWER_S: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::S);
    pub const LOWER_T: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::T);
    pub const LOWER_U: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::U);
    pub const LOWER_V: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::V);
    pub const LOWER_W: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::W);
    pub const LOWER_X: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::X);
    pub const LOWER_Y: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::Y);
    pub const LOWER_Z: Self = LxMathLetter::LowerLatin(LxMathLatinLetter::Z);
}
