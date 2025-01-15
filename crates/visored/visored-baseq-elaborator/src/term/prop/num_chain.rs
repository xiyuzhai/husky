use super::*;

#[floated(constructor = pub new)]
pub struct VdBsqNumChain<'sess> {
    pub leader: VdBsqNumTerm<'sess>,
    #[return_ref]
    pub followers: Vec<(VdMirFunc, VdBsqNumTerm<'sess>)>,
}

impl<'sess> From<VdBsqNumChain<'sess>> for VdBsqTerm<'sess> {
    fn from(chain: VdBsqNumChain<'sess>) -> Self {
        VdBsqTerm::Prop(chain.into())
    }
}

impl<'db, 'sess> VdBsqNumChain<'sess> {
    pub(crate) fn transcribe(
        self,
        elaborator: &VdBsqElaboratorInner<'db, 'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprData {
        todo!()
    }
}
