use husky_entity_path::path::major_item::ty::{OtherTypePath, PreludeTypePath, TypePath};

use super::*;

impl FlyTerm {
    #[inline(always)]
    pub fn new_application(
        engine: &mut impl FlyTermEngineMut,
        function: impl Into<FlyTerm>,
        argument: impl Into<FlyTerm>,
    ) -> EthTermResult<Self> {
        let db = engine.db();
        let function = function.into();
        let argument = argument.into();
        match (
            function.base_resolved(engine),
            argument.base_resolved(engine),
        ) {
            (FlyTermBase::Eth(function), FlyTermBase::Eth(argument)) => {
                Ok(EthApplication::new(db, function, argument)?.into())
            }
            (
                FlyTermBase::Eth(_) | FlyTermBase::Sol(_),
                FlyTermBase::Eth(_) | FlyTermBase::Sol(_),
            ) => {
                todo!()
            }
            _ => {
                let data = match function.base_term_data(engine) {
                    FlyTermData::TypeOntology {
                        ty_path: path,
                        refined_ty_path: refined_path,
                        ty_arguments: arguments,
                        ..
                    } => {
                        let mut arguments = arguments.to_smallvec();
                        arguments.push(argument.into());
                        HolTermData::TypeOntology {
                            path,
                            refined_path,
                            arguments,
                        }
                    }
                    FlyTermData::Trait { .. } => todo!(),
                    FlyTermData::Hole(_, _) => todo!(),
                    FlyTermData::SymbolicVariable { .. } => todo!(),
                    FlyTermData::AbstractVariable { .. } => todo!(),
                    FlyTermData::TypeVariant { .. } => todo!(),
                    FlyTermData::Sort(_)
                    | FlyTermData::Literal(_)
                    | FlyTermData::Curry { .. }
                    | FlyTermData::Ritchie { .. } => unreachable!(),
                    FlyTermData::MajorTypeVar(_) => todo!(),
                };
                Ok(HolTerm::new(engine, data).into())
            }
        }
    }

    pub fn leashed(self, engine: &mut impl FlyTermEngineMut) -> EthTermResult<Self> {
        let function: FlyTerm = engine.term_menu().leash_ty_ontology().into();
        Self::new_application(engine, function, self)
    }

    pub fn new_ty_ontology(
        db: &::salsa::Db,
        fly_terms: &mut FlyTerms,
        path: TypePath,
        refined_path: Either<PreludeTypePath, OtherTypePath>,
        arguments: SmallVec<[FlyTerm; 2]>,
    ) -> Self {
        if arguments.len() == 0 {
            ItemPathTerm::TypeOntology(path).into()
        } else {
            let mut merger = FlyTermDataKindMerger::new(fly_terms);
            merger.accept(arguments.iter().copied());
            match merger.data_kind() {
                FlyTermDataKind::Ethereal => {
                    match EthTerm::new_ty_ontology(
                        db,
                        path,
                        arguments.iter().map(|argument| {
                            match argument.resolve_progress(fly_terms) {
                                TermResolveProgress::ResolvedEth(argument) => argument,
                                _ => unreachable!(),
                            }
                        }),
                    ) {
                        Ok(term) => term.into(),
                        Err(_) => todo!(),
                    }
                }
                FlyTermDataKind::Solid => fly_terms
                    .sol_terms_mut()
                    .intern_new(SolTermData::TypeOntology {
                        path,
                        refined_path,
                        arguments,
                    })
                    .into(),
                FlyTermDataKind::Hollow => fly_terms
                    .hol_terms_mut()
                    .alloc_new(HolTermData::TypeOntology {
                        path,
                        refined_path,
                        arguments,
                    })
                    .into(),
                FlyTermDataKind::Err => todo!(),
            }
        }
    }
}
