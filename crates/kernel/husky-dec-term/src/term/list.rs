use super::*;

#[salsa::interned]
pub struct DecList {
    pub toolchain: Toolchain,
    #[return_ref]
    pub items: Vec<DecTerm>,
}

impl DecList {
    pub(crate) fn display_fmt_with_db_and_ctx(
        self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
        ctx: &DecSymbolicVariableNameMap,
    ) -> std::fmt::Result {
        f.write_str("[")?;
        let items = self.items(db);
        for (i, item) in items.iter().enumerate() {
            item.display_fmt_with_db_and_ctx(f, db, ctx)?;
            if i < items.len() {
                f.write_str(", ")?
            }
        }
        f.write_str("]")
    }
}
