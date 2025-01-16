use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseChainingSeparator {
    Iff,
    Relation(VdMirBaseRelationSeparator),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseRelationSeparator {
    Comparison(VdMirBaseComparisonSeparator),
    Containment(VdMirBaseContainmentSeparator),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseComparisonSeparator {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseContainmentSeparator {
    In,
    Notin,
    Subset,
    Supset,
    Subseteq,
    Supseteq,
    Subseteqq,
    Supseteqq,
    Subsetneq,
    Supsetneq,
}

impl VdMirBaseContainmentSeparator {
    pub const SUBSET: Self = VdMirBaseContainmentSeparator::Subset;
    pub const SUPSET: Self = VdMirBaseContainmentSeparator::Supset;
    pub const SUBSETEQ: Self = VdMirBaseContainmentSeparator::Subseteq;
    pub const SUPSETEQ: Self = VdMirBaseContainmentSeparator::Supseteq;
    pub const SUBSETEQQ: Self = VdMirBaseContainmentSeparator::Subseteqq;
    pub const SUPSETEQQ: Self = VdMirBaseContainmentSeparator::Supseteqq;
    pub const SUBSETNEQ: Self = VdMirBaseContainmentSeparator::Subsetneq;
    pub const SUPSETNEQ: Self = VdMirBaseContainmentSeparator::Supsetneq;
}

impl VdMirBaseComparisonSeparator {
    pub const EQ: Self = VdMirBaseComparisonSeparator::Eq;
    pub const NE: Self = VdMirBaseComparisonSeparator::Ne;
    pub const LT: Self = VdMirBaseComparisonSeparator::Lt;
    pub const GT: Self = VdMirBaseComparisonSeparator::Gt;
    pub const LE: Self = VdMirBaseComparisonSeparator::Le;
    pub const GE: Self = VdMirBaseComparisonSeparator::Ge;
}

impl VdMirBaseRelationSeparator {
    pub const EQ: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::EQ);
    pub const NE: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::NE);
    pub const LT: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::LT);
    pub const GT: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::GT);
    pub const LE: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::LE);
    pub const GE: Self = VdMirBaseRelationSeparator::Comparison(VdMirBaseComparisonSeparator::GE);
    pub const SUBSET: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUBSET);
    pub const SUPSET: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUPSET);
    pub const SUBSETEQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUBSETEQ);
    pub const SUPSETEQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUPSETEQ);
    pub const SUBSETEQQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUBSETEQQ);
    pub const SUPSETEQQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUPSETEQQ);
    pub const SUBSETNEQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUBSETNEQ);
    pub const SUPSETNEQ: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::SUPSETNEQ);
}

impl VdMirBaseChainingSeparator {
    pub const IFF: Self = VdMirBaseChainingSeparator::Iff;
    pub const EQ: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::EQ);
    pub const NE: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::NE);
    pub const LT: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::LT);
    pub const GT: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::GT);
    pub const LE: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::LE);
    pub const GE: Self = VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::GE);
    pub const SUBSET: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUBSET);
    pub const SUPSET: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUPSET);
    pub const SUBSETEQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUBSETEQ);
    pub const SUPSETEQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUPSETEQ);
    pub const SUBSETEQQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUBSETEQQ);
    pub const SUPSETEQQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUPSETEQQ);
    pub const SUBSETNEQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUBSETNEQ);
    pub const SUPSETNEQ: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::SUPSETNEQ);
}

impl VdMirBaseChainingSeparator {
    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdMirBaseChainingSeparator::Relation(relation) => VdSeparatorClass::Relation,
            VdMirBaseChainingSeparator::Iff => VdSeparatorClass::Deduction,
        }
    }

    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseChainingSeparator::Relation(relation) => relation.unicode(),
            VdMirBaseChainingSeparator::Iff => "⟺",
        }
    }

    pub fn is_equivalence(self) -> bool {
        match self {
            VdMirBaseChainingSeparator::Iff => true,
            VdMirBaseChainingSeparator::Relation(slf) => slf.is_equivalence(),
        }
    }
}

impl VdMirBaseRelationSeparator {
    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseRelationSeparator::Comparison(comparison) => comparison.unicode(),
            VdMirBaseRelationSeparator::Containment(containment) => containment.unicode(),
        }
    }

    pub fn is_equivalence(self) -> bool {
        match self {
            VdMirBaseRelationSeparator::Comparison(slf) => slf.is_equivalence(),
            VdMirBaseRelationSeparator::Containment(slf) => false,
        }
    }
}

impl VdMirBaseComparisonSeparator {
    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseComparisonSeparator::Eq => "=",
            VdMirBaseComparisonSeparator::Ne => "≠",
            VdMirBaseComparisonSeparator::Lt => "<",
            VdMirBaseComparisonSeparator::Gt => ">",
            VdMirBaseComparisonSeparator::Le => "≤",
            VdMirBaseComparisonSeparator::Ge => "≥",
        }
    }

    pub fn is_equivalence(self) -> bool {
        match self {
            VdMirBaseComparisonSeparator::Eq => true,
            _ => false,
        }
    }
}

impl VdMirBaseContainmentSeparator {
    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseContainmentSeparator::In => "∈",
            VdMirBaseContainmentSeparator::Notin => "∉",
            VdMirBaseContainmentSeparator::Subset => "⊂",
            VdMirBaseContainmentSeparator::Supset => "⊃",
            VdMirBaseContainmentSeparator::Subseteq => "⊆",
            VdMirBaseContainmentSeparator::Supseteq => "⊇",
            VdMirBaseContainmentSeparator::Subseteqq => "⫅",
            VdMirBaseContainmentSeparator::Supseteqq => "⫆",
            VdMirBaseContainmentSeparator::Subsetneq => "⊊",
            VdMirBaseContainmentSeparator::Supsetneq => "⊋",
        }
    }
}
