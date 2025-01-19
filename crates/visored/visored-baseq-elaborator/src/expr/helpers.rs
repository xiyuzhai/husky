use super::*;

impl<'sess> VdBsqExpr<'sess> {
    pub fn is_zero(self) -> bool {
        self.eqs_nat128(0)
    }

    pub fn is_one(self) -> bool {
        self.eqs_nat128(1)
    }

    pub fn eqs_nat128(self, i: i128) -> bool {
        use num_traits::ToPrimitive;

        let VdBsqExprData::Literal(lit) = self.data() else {
            return false;
        };
        let VdLiteralData::Int(ref i1) = *lit.data() else {
            return false;
        };
        i1.to_i128() == Some(i)
    }
}
