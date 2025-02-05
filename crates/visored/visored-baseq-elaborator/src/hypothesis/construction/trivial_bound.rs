use crate::foundations::num::VdBsqSign;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBsqTrivialBoundHypothesisConstruction {
    EvenPower { sign: VdBsqSign },
}
