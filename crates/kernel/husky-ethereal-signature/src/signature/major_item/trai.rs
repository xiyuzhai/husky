use super::*;

#[salsa::interned(db = EtherealSignatureDb, jar = EtherealSignatureJar)]
pub struct TraitEtherealSignatureTemplate {
    pub path: TraitPath,
    #[return_ref]
    pub template_parameters: EtherealTermTemplateParameters,
}

impl HasEtherealSignatureTemplate for TraitPath {
    type EtherealSignatureTemplate = TraitEtherealSignatureTemplate;

    fn ethereal_signature_template(
        self,
        db: &dyn EtherealSignatureDb,
    ) -> EtherealSignatureResult<Self::EtherealSignatureTemplate> {
        trai_ethereal_signature_template(db, self)
    }
}

#[salsa::tracked(jar = EtherealSignatureJar)]
fn trai_ethereal_signature_template(
    db: &dyn EtherealSignatureDb,
    trai_path: TraitPath,
) -> EtherealSignatureResult<TraitEtherealSignatureTemplate> {
    let declarative_signature_template = trai_path.declarative_signature_template(db)?;
    let template_parameters = EtherealTermTemplateParameters::from_declarative(
        db,
        declarative_signature_template.template_parameters(db),
    )?;
    Ok(TraitEtherealSignatureTemplate::new(
        db,
        trai_path,
        template_parameters,
    ))
}