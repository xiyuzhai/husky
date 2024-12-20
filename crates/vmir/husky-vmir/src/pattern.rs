pub mod destructive;
pub mod restructive;

use self::{
    destructive::VmirDestructivePattern, eval::EvalVmir, restructive::VmirRestructivePattern,
};
use crate::*;
use husky_hir_eager_expr::{HirEagerPatternData, HirEagerPatternIdx};
use husky_linket_impl::linket_impl::LinketImplThawedValue;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VmirPattern<LinketImpl: IsLinketImpl> {
    /// a restructive version is always needed to tell if pattern is satisfied
    restructive_pattern: VmirRestructivePattern<LinketImpl>,
    /// only need this for destructive pattern
    destructive_pattern: Option<VmirDestructivePattern<LinketImpl>>,
}

impl<LinketImpl: IsLinketImpl> VmirPattern<LinketImpl> {
    /// a restructive version is always needed to tell if pattern is satisfied
    pub fn restructive_pattern(self) -> VmirRestructivePattern<LinketImpl> {
        self.restructive_pattern
    }

    /// only need this for destructive pattern
    pub fn destructive_pattern(self) -> Option<VmirDestructivePattern<LinketImpl>> {
        self.destructive_pattern
    }
}

impl<LinketImpl: IsLinketImpl> ToVmir<LinketImpl> for HirEagerPatternIdx {
    type Output = VmirPattern<LinketImpl>;

    fn to_vmir<Linktime>(self, builder: &mut VmirBuilder<Linktime>) -> Self::Output
    where
        Linktime: IsLinktime<LinketImpl = LinketImpl>,
    {
        let restructive_pattern = builder.build_restructive_pattern(self);
        let destructive_pattern = builder.build_destructive_pattern(self);
        VmirPattern {
            restructive_pattern,
            destructive_pattern,
        }
    }
}

impl<'comptime, LinketImpl: IsLinketImpl> VmirPattern<LinketImpl> {
    pub(crate) fn take_value(
        self,
        value: LinketImplThawedValue<LinketImpl>,
        ctx: &mut impl EvalVmir<'comptime, LinketImpl>,
    ) {
        if let Some(destructive_pattern) = self.destructive_pattern {
            destructive_pattern.take_value(value, ctx);
        } else {
            self.restructive_pattern.take_value(value, ctx);
        }
    }
}
