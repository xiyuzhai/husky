#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum VdDivisionLevel {
    Part,
    Chapter,
    Section,
    Subsection,
    Subsubsection,
    Stmts,
}

impl std::fmt::Display for VdDivisionLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.code_name())
    }
}

impl VdDivisionLevel {
    pub fn code_name(&self) -> &'static str {
        match self {
            VdDivisionLevel::Part => "part",
            VdDivisionLevel::Chapter => "chapter",
            VdDivisionLevel::Section => "section",
            VdDivisionLevel::Subsection => "subsection",
            VdDivisionLevel::Subsubsection => "subsubsection",
            VdDivisionLevel::Stmts => "stmts",
        }
    }

    pub fn uppercase_code_name(&self) -> &'static str {
        match self {
            VdDivisionLevel::Part => "Part",
            VdDivisionLevel::Chapter => "Chapter",
            VdDivisionLevel::Section => "Section",
            VdDivisionLevel::Subsection => "Subsection",
            VdDivisionLevel::Subsubsection => "Subsubsection",
            VdDivisionLevel::Stmts => "Stmts",
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum VdDivisionLevelRange {
    Any,
    Below(VdDivisionLevel),
}

impl VdDivisionLevelRange {
    pub const ANY: Self = VdDivisionLevelRange::Any;
}

impl VdDivisionLevelRange {
    pub fn contains(self, level: VdDivisionLevel) -> bool {
        match self {
            VdDivisionLevelRange::Any => true,
            VdDivisionLevelRange::Below(vd_division_level) => level > vd_division_level,
        }
    }
}

#[cfg(test)]
#[test]
fn test_division_level_range_contains() {
    // Test Any range
    let any_range = VdDivisionLevelRange::Any;
    assert!(any_range.contains(VdDivisionLevel::Part));
    assert!(any_range.contains(VdDivisionLevel::Stmts));

    // Test NoLessThan range
    let below_chapter = VdDivisionLevelRange::Below(VdDivisionLevel::Chapter);
    assert!(!below_chapter.contains(VdDivisionLevel::Part));
    assert!(!below_chapter.contains(VdDivisionLevel::Chapter));
    assert!(below_chapter.contains(VdDivisionLevel::Section));
    assert!(below_chapter.contains(VdDivisionLevel::Subsection));
    assert!(below_chapter.contains(VdDivisionLevel::Subsubsection));
    assert!(below_chapter.contains(VdDivisionLevel::Stmts));
}
