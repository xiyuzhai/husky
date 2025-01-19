use super::*;
use latex_math_letter::letter::LxMathLetter;
use visored_mir_expr::symbol::local_defn::VdMirSymbolLocalDefnIdx;
use visored_opr::precedence::VdPrecedenceRange;

#[floated]
pub struct VdBsqAtomTerm<'sess> {
    #[return_ref]
    data: VdBsqComnumAtomTermData,
}

impl<'sess> std::fmt::Debug for VdBsqAtomTerm<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("AtomTerm(`")?;
        self.data().show_fmt(VdPrecedenceRange::Any, f)?;
        f.write_str("`)")
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqComnumAtomTermData {
    Variable {
        lx_math_letter: LxMathLetter,
        local_defn_idx: VdMirSymbolLocalDefnIdx,
        ty: VdType,
    },
}

impl<'sess> From<VdBsqAtomTerm<'sess>> for VdBsqNumTerm<'sess> {
    fn from(value: VdBsqAtomTerm<'sess>) -> Self {
        VdBsqNumTerm::Comnum(VdBsqComnumTerm::Atom(value))
    }
}

impl<'sess> VdBsqComnumTerm<'sess> {
    pub fn new_atom(data: VdBsqComnumAtomTermData, db: &'sess FloaterDb) -> Self {
        VdBsqComnumTerm::Atom(VdBsqAtomTerm::new_inner(data, db))
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn new_numeric_variable(
        lx_math_letter: LxMathLetter,
        local_defn_idx: VdMirSymbolLocalDefnIdx,
        ty: VdType,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqTerm::Comnum(VdBsqComnumTerm::Atom(VdBsqAtomTerm::new_inner(
            VdBsqComnumAtomTermData::Variable {
                lx_math_letter,
                local_defn_idx,
                ty,
            },
            db,
        )))
    }
}

impl<'sess> VdBsqAtomTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.data().show_fmt(precedence_range, f)
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        self.data().outer_precedence()
    }
}

impl<'sess> VdBsqComnumAtomTermData {
    pub fn show_fmt(
        &self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VdBsqComnumAtomTermData::Variable { lx_math_letter, .. } => {
                write!(f, "{}", lx_math_letter.unicode())
            }
        }
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdBsqComnumAtomTermData::Variable { .. } => VdPrecedence::ATOM,
        }
    }
}

impl<'sess> VdBsqAtomTerm<'sess> {
    pub fn neg(self, db: &'sess FloaterDb) -> VdBsqProductTerm<'sess> {
        match VdBsqProductTerm::new(-1, self) {
            VdBsqNumTerm::Comnum(VdBsqComnumTerm::Product(product)) => product,
            _ => unreachable!(),
        }
    }

    pub fn mul_litnum(
        self,
        rhs: impl Into<VdBsqLitnumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        let rhs = rhs.into();
        if rhs == 0.into() {
            return VdBsqNumTerm::ZERO;
        }
        if rhs == 1.into() {
            return self.into();
        }
        VdBsqProductTerm::new(rhs, self).into()
    }

    pub fn div_litnum(
        self,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqComnumTerm<'sess>> {
        if rhs == 0.into() {
            return None;
        }
        if rhs == 1.into() {
            return Some(self.into());
        }
        match VdBsqProductTerm::new(rhs.inverse().unwrap(), self) {
            VdBsqNumTerm::Litnum(_) => unreachable!(),
            VdBsqNumTerm::Comnum(comnum) => Some(comnum),
        }
    }
}

impl<'db, 'sess> VdBsqAtomTerm<'sess> {
    pub(crate) fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprFld<'sess> {
        let (expr_data, ty) = self.expr_data_and_ty(elr, hc);
        elr.mk_expr(expr_data, ty)
    }

    fn expr_data_and_ty(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdBsqExprData<'sess>, VdType) {
        match *self.data() {
            VdBsqComnumAtomTermData::Variable {
                lx_math_letter,
                local_defn_idx,
                ty,
            } => (VdBsqExprData::Variable(lx_math_letter, local_defn_idx), ty),
        }
    }
}
