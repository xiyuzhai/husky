use super::*;

pub struct DecTermSubstitution {
    src: DecAbstractVariable,
    dst: DecTerm,
}

impl DecTermSubstitution {
    pub fn new(src: DecAbstractVariable, dst: DecTerm) -> Self {
        Self { src, dst }
    }

    pub(crate) fn src(&self) -> DecAbstractVariable {
        self.src
    }

    pub(crate) fn dst(&self) -> DecTerm {
        self.dst
    }
}
