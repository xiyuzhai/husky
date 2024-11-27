use super::*;
use expr::VdSynExprArenaRef;

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub fn show(&self) -> String {
        format!(
            "{}",
            self.stack.show(self.builder.expr_arena().as_arena_ref())
        )
    }
}
