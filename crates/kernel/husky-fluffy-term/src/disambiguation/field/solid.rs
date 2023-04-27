use super::*;

impl SolidTerm {
    pub(super) fn field_disambiguation_aux(
        self,
        engine: &mut impl FluffyTermEngine,
        ident: Ident,
        available_traits: &[TraitPath],
        mut indirections: SmallVec<[FluffyIndirection; 2]>,
    ) -> FluffyTermMaybeResult<FluffyFieldDisambiguation> {
        match self.data(engine) {
            SolidTermData::TypeOntology {
                path,
                refined_path,
                arguments,
            } => todo!(),
            SolidTermData::PlaceTypeOntology {
                place,
                path,
                refined_path,
                arguments,
                base_ty_term,
            } => match base_ty_term {
                Some(base_ty_term) => {
                    indirections.push(FluffyIndirection::Place(*place));
                    JustOk(
                        ethereal_ty_field_disambiguation(engine.db(), *base_ty_term, ident)?
                            .merge(indirections),
                    )
                }
                None => todo!(),
            },
            SolidTermData::Curry { .. } | SolidTermData::Ritchie { .. } => Nothing,
        }
    }
}