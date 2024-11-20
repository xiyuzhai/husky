use super::*;
use helpers::trai_for_ty::is_ty_term_always_copyable;
use husky_dec_signature::signature::major_item::form::val::MajorValDecTemplate;

#[salsa::interned]
pub struct MajorValEthTemplate {
    pub path: MajorFormPath,
    /// the type of the definition body
    pub return_ty: EthTerm,
    /// the type of the expression when used
    // TODO: maybe rename as output_ty?
    pub expr_ty: EthTerm,
}

impl MajorValEthTemplate {
    pub(super) fn from_dec(
        db: &::salsa::Db,
        path: MajorFormPath,
        dec_template: MajorValDecTemplate,
    ) -> EthSignatureResult<Self> {
        let return_ty = EthTerm::ty_from_dec(db, dec_template.return_ty(db))?;
        let expr_ty = if is_ty_term_always_copyable(return_ty, db)?.unwrap() {
            return_ty
        } else {
            return_ty.leashed(db)
        };
        Ok(Self::new(db, path, return_ty, expr_ty))
    }
}
