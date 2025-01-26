use crate::*;
use lean_mir_expr::expr::LnMirExprEntry;
use visored_mir_expr::coercion::VdMirCoercion;

impl<S> VdTranspileToLean<S, LnMirExprEntry> for VdMirCoercion
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
        todo!()
    }
}
