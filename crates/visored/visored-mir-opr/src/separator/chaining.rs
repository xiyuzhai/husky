use visored_opr::separator::VdBaseSeparator;

use super::*;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseChainingSeparator {
    Iff,
    Relation(VdMirBaseRelationSeparator),
}

#[enum_class::from_variants]
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

impl From<VdMirBaseComparisonSeparator> for VdMirBaseSeparator {
    fn from(separator: VdMirBaseComparisonSeparator) -> Self {
        VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::Relation(
            VdMirBaseRelationSeparator::Comparison(separator),
        ))
    }
}

impl From<VdMirBaseComparisonSeparator> for VdBaseSeparator {
    fn from(separator: VdMirBaseComparisonSeparator) -> Self {
        match separator {
            VdMirBaseComparisonSeparator::Eq => VdBaseSeparator::Eq,
            VdMirBaseComparisonSeparator::Ne => VdBaseSeparator::Ne,
            VdMirBaseComparisonSeparator::Lt => VdBaseSeparator::Lt,
            VdMirBaseComparisonSeparator::Gt => VdBaseSeparator::Gt,
            VdMirBaseComparisonSeparator::Le => VdBaseSeparator::Le,
            VdMirBaseComparisonSeparator::Ge => VdBaseSeparator::Ge,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseContainmentSeparator {
    InSet,
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

impl From<VdMirBaseContainmentSeparator> for VdBaseSeparator {
    fn from(separator: VdMirBaseContainmentSeparator) -> Self {
        match separator {
            VdMirBaseContainmentSeparator::InSet => VdBaseSeparator::In,
            VdMirBaseContainmentSeparator::Notin => VdBaseSeparator::Notin,
            VdMirBaseContainmentSeparator::Subset => VdBaseSeparator::Subset,
            VdMirBaseContainmentSeparator::Supset => VdBaseSeparator::Supset,
            VdMirBaseContainmentSeparator::Subseteq => VdBaseSeparator::Subseteq,
            VdMirBaseContainmentSeparator::Supseteq => VdBaseSeparator::Supseteq,
            VdMirBaseContainmentSeparator::Subseteqq => VdBaseSeparator::Subseteqq,
            VdMirBaseContainmentSeparator::Supseteqq => VdBaseSeparator::Supseteqq,
            VdMirBaseContainmentSeparator::Subsetneq => VdBaseSeparator::Subsetneq,
            VdMirBaseContainmentSeparator::Supsetneq => VdBaseSeparator::Supsetneq,
        }
    }
}

impl VdMirBaseContainmentSeparator {
    pub const IN_SET: Self = VdMirBaseContainmentSeparator::InSet;
    pub const NOT_IN_SET: Self = VdMirBaseContainmentSeparator::Notin;
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
    pub const IN_SET: Self =
        VdMirBaseRelationSeparator::Containment(VdMirBaseContainmentSeparator::IN_SET);
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
    pub const IN_SET: Self =
        VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::IN_SET);
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

    pub fn outer_precedence(&self) -> VdPrecedence {
        self.class().precedence()
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        self.class().right_precedence_range()
    }

    pub fn show_fmt(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.unicode())
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
            VdMirBaseContainmentSeparator::InSet => "∈",
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

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        todo!()
    }
}
