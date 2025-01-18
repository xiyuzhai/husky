use super::*;
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

#[floated(constructor = pub new)]
pub struct VdBsqNumChain<'sess> {
    pub leader: VdBsqNumTerm<'sess>,
    #[return_ref]
    pub followers: Vec<(VdBaseChainingSeparatorSignature, VdBsqNumTerm<'sess>)>,
}

impl<'sess> From<VdBsqNumChain<'sess>> for VdBsqTerm<'sess> {
    fn from(chain: VdBsqNumChain<'sess>) -> Self {
        VdBsqTerm::Prop(chain.into())
    }
}

impl<'db, 'sess> VdBsqNumChain<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let outer_precedence = self.followers()[0].0.separator().outer_precedence();
        if precedence_range.contains(outer_precedence) {
            self.show_fmt_inner(precedence_range, f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(precedence_range, f)?;
            f.write_str(")")
        }
    }

    fn show_fmt_inner(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.leader().show_fmt(precedence_range, f)?;
        for &(signature, follower) in self.followers() {
            signature.separator().show_fmt(f)?;
            follower.show_fmt(precedence_range, f)?;
        }
        Ok(())
    }
}

impl<'db, 'sess> VdBsqNumChain<'sess> {
    pub(crate) fn transcribe(
        self,
        elaborator: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprData {
        todo!()
    }
}
