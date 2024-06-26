use crate::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[enum_class::from_variants]
pub enum BinaryShiftOpr {
    Shl,
    Shr,
}

impl BinaryShiftOpr {
    pub fn rust_trait_method_name(self) -> &'static str {
        match self {
            BinaryShiftOpr::Shl => todo!(),
            BinaryShiftOpr::Shr => todo!(),
        }
    }

    pub fn husky_code(self) -> &'static str {
        match self {
            BinaryShiftOpr::Shl => "<<",
            BinaryShiftOpr::Shr => ">>",
        }
    }

    pub fn spaced_husky_code(self) -> &'static str {
        match self {
            BinaryShiftOpr::Shl => " << ",
            BinaryShiftOpr::Shr => " >> ",
        }
    }
}

impl HasPrecedence for BinaryShiftOpr {
    #[inline(always)]
    fn precedence(self) -> Precedence {
        Precedence::Shift
    }
}
