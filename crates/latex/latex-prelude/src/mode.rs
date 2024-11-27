use std::num::NonZeroU64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxMode {
    Lisp,
    Math,
    Root,
    Rose,
    Name,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxModeSet(NonZeroU64);

impl LxModeSet {
    pub const LISP: Self = Self(unsafe { NonZeroU64::new_unchecked(1 << 1 + 1) });
    pub const MATH: Self = Self(unsafe { NonZeroU64::new_unchecked(1 << 2 + 1) });
    pub const ROOT: Self = Self(unsafe { NonZeroU64::new_unchecked(1 << 3 + 1) });
    pub const ROSE: Self = Self(unsafe { NonZeroU64::new_unchecked(1 << 4 + 1) });
    pub const NAME: Self = Self(unsafe { NonZeroU64::new_unchecked(1 << 5 + 1) });
}

impl LxModeSet {
    pub fn allowed_in_lisp(self) -> bool {
        self.0.get() & Self::LISP.0.get() != 0
    }

    pub fn allowed_in_math(self) -> bool {
        self.0.get() & Self::MATH.0.get() != 0
    }

    pub fn allowed_in_root(self) -> bool {
        self.0.get() & Self::ROOT.0.get() != 0
    }

    pub fn allowed_in_rose(self) -> bool {
        self.0.get() & Self::ROSE.0.get() != 0
    }

    pub fn allowed_in_name(self) -> bool {
        self.0.get() & Self::NAME.0.get() != 0
    }
}

impl std::ops::BitOr for LxModeSet {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for LxModeSet {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl<I> From<I> for LxModeSet
where
    I: IntoIterator<Item = LxMode>,
{
    fn from(modes: I) -> Self {
        modes.into_iter().collect()
    }
}

impl FromIterator<LxMode> for LxModeSet {
    fn from_iter<T: IntoIterator<Item = LxMode>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Self::LISP, |acc, mode| acc | mode.into())
    }
}

impl From<LxMode> for LxModeSet {
    fn from(mode: LxMode) -> Self {
        match mode {
            LxMode::Lisp => Self::LISP,
            LxMode::Math => Self::MATH,
            LxMode::Root => Self::ROOT,
            LxMode::Rose => Self::ROSE,
            LxMode::Name => Self::NAME,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_modes() {
        assert!(LxModeSet::LISP.allowed_in_lisp());
        assert!(!LxModeSet::LISP.allowed_in_math());
        assert!(!LxModeSet::LISP.allowed_in_root());
        assert!(!LxModeSet::LISP.allowed_in_rose());
        assert!(!LxModeSet::LISP.allowed_in_name());

        assert!(!LxModeSet::MATH.allowed_in_lisp());
        assert!(LxModeSet::MATH.allowed_in_math());
        assert!(!LxModeSet::MATH.allowed_in_root());
        assert!(!LxModeSet::MATH.allowed_in_rose());
        assert!(!LxModeSet::MATH.allowed_in_name());

        assert!(!LxModeSet::ROOT.allowed_in_lisp());
        assert!(!LxModeSet::ROOT.allowed_in_math());
        assert!(LxModeSet::ROOT.allowed_in_root());
        assert!(!LxModeSet::ROOT.allowed_in_rose());
        assert!(!LxModeSet::ROOT.allowed_in_name());

        assert!(!LxModeSet::ROSE.allowed_in_lisp());
        assert!(!LxModeSet::ROSE.allowed_in_math());
        assert!(!LxModeSet::ROSE.allowed_in_root());
        assert!(LxModeSet::ROSE.allowed_in_rose());
        assert!(!LxModeSet::ROSE.allowed_in_name());

        assert!(!LxModeSet::NAME.allowed_in_lisp());
        assert!(!LxModeSet::NAME.allowed_in_math());
        assert!(!LxModeSet::NAME.allowed_in_root());
        assert!(!LxModeSet::NAME.allowed_in_rose());
        assert!(LxModeSet::NAME.allowed_in_name());
    }

    #[test]
    fn test_mode_combinations() {
        let combined = LxModeSet::LISP | LxModeSet::MATH;
        assert!(combined.allowed_in_lisp());
        assert!(combined.allowed_in_math());
        assert!(!combined.allowed_in_root());
        assert!(!combined.allowed_in_rose());
        assert!(!combined.allowed_in_name());

        let all_modes =
            LxModeSet::LISP | LxModeSet::MATH | LxModeSet::ROOT | LxModeSet::ROSE | LxModeSet::NAME;
        assert!(all_modes.allowed_in_lisp());
        assert!(all_modes.allowed_in_math());
        assert!(all_modes.allowed_in_root());
        assert!(all_modes.allowed_in_rose());
        assert!(all_modes.allowed_in_name());
    }

    #[test]
    fn test_from_slice() {
        let modes = &[LxMode::Lisp, LxMode::Math, LxMode::Root];
        let set: LxModeSet = modes.iter().copied().collect();
        assert!(set.allowed_in_lisp());
        assert!(set.allowed_in_math());
        assert!(set.allowed_in_root());
        assert!(!set.allowed_in_rose());
        assert!(!set.allowed_in_name());
    }

    #[test]
    fn test_bitor_assign() {
        let mut set = LxModeSet::LISP;
        set |= LxModeSet::MATH;
        assert!(set.allowed_in_lisp());
        assert!(set.allowed_in_math());
        assert!(!set.allowed_in_root());
    }

    #[test]
    fn test_from_mode() {
        let set = LxModeSet::from(LxMode::Lisp);
        assert!(set.allowed_in_lisp());
        assert!(!set.allowed_in_math());
        assert!(!set.allowed_in_root());
        assert!(!set.allowed_in_rose());
        assert!(!set.allowed_in_name());
    }
}
