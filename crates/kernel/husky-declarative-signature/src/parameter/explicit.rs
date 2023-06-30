use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct ExplicitParameterDeclarativeSignature {
    contract: Contract,
    ty: DeclarativeTerm,
}

impl ExplicitParameterDeclarativeSignature {
    pub fn into_ritchie_parameter_contracted_ty(
        self,
    ) -> DeclarativeTermRitchieParameterContractedType {
        DeclarativeTermRitchieParameterContractedType::new(self.contract, self.ty)
    }
}

impl ExplicitParameterDeclarativeSignature {
    pub(crate) fn new(contract: Contract, ty: DeclarativeTerm) -> Self {
        Self { contract, ty }
    }

    pub fn contract(&self) -> Contract {
        self.contract
    }

    pub fn ty(&self) -> DeclarativeTerm {
        self.ty
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ExplicitParameterDeclarativeSignatureTemplates {
    data: SmallVec<[ExplicitParameterDeclarativeSignature; 4]>,
}

impl std::ops::Deref for ExplicitParameterDeclarativeSignatureTemplates {
    type Target = [ExplicitParameterDeclarativeSignature];

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl ExplicitParameterDeclarativeSignatureTemplates {
    pub(crate) fn from_decl(
        parameters: &[RegularParameterDeclPattern],
        expr_region_data: &ExprRegionData,
        signature_region: &DeclarativeTermRegion,
    ) -> DeclarativeSignatureResult<Self> {
        Ok(Self {
            data: parameters
                .iter()
                .enumerate()
                .map(|(i, parameter)| {
                    let ty = parameter.ty();
                    parameter.pattern();
                    let ty = match signature_region.expr_term(ty) {
                        Ok(ty) => ty,
                        Err(_) => {
                            return Err(
                                DeclarativeSignatureError::ParameterTypeDeclarativeTermError(
                                    i.try_into().unwrap(),
                                ),
                            )
                        }
                    };
                    Ok(ExplicitParameterDeclarativeSignature::new(
                        expr_region_data.pattern_contract(parameter.pattern()),
                        ty,
                    ))
                })
                .collect::<DeclarativeSignatureResult<_>>()?,
        })
    }
}