use crate::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FlyTermSubstitution {
    hvar: FlyHvar,
    substitute: FlyTerm,
}

pub type ImplicitParameterSubstitutions = SmallVec<[FlyTermSubstitution; 2]>;

impl FlyTermSubstitution {
    fn new(hvar: FlyHvar, substitute: impl Into<FlyTerm>) -> Self {
        Self {
            hvar,
            substitute: substitute.into(),
        }
    }

    /// this will collect implicit parameters and give rules that replace them with holes
    pub(crate) fn from_expectee(
        expectee: FlyTerm,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        idx: FlyTermExpectationIdx,
    ) -> (FlyTerm, ImplicitParameterSubstitutions) {
        Self::from_expectee_aux(expectee, db, terms, idx, smallvec![])
    }

    fn from_expectee_aux(
        expectee: FlyTerm,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        idx: FlyTermExpectationIdx,
        mut template_parameter_substitutions: ImplicitParameterSubstitutions,
    ) -> (FlyTerm, ImplicitParameterSubstitutions) {
        match expectee.base_term_data2(db, terms) {
            FlyTermData::Curry {
                toolchain,
                curry_kind: CurryKind::Implicit,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => {
                let parameter_hvar = parameter_hvar
                    .expect("curry type with implicit parameter should be dependent type");
                let implicit_symbol = terms.new_hole_from_parameter_hvar(
                    db,
                    HoleSource::Expectation(idx),
                    parameter_hvar,
                );
                template_parameter_substitutions
                    .push(FlyTermSubstitution::new(parameter_hvar, implicit_symbol));
                let expectee = return_ty.rewrite_inner(
                    db,
                    terms,
                    HoleSource::Expectation(idx),
                    &template_parameter_substitutions,
                );
                Self::from_expectee_aux(expectee, db, terms, idx, template_parameter_substitutions)
            }
            _ => (expectee, template_parameter_substitutions),
        }
    }
}

impl FlyTerm {
    pub fn substitute_hvar(
        self,
        engine: &mut impl FlyTermEngineMut,
        src: HoleSource,
        hvar: FlyHvar,
        substitute: FlyTerm,
    ) -> Self {
        self.rewrite_inner(
            engine.db(),
            engine.fly_terms_mut(),
            src,
            &[FlyTermSubstitution::new(hvar, substitute)],
        )
    }

    pub(crate) fn rewrite_inner(
        self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        src: HoleSource,
        substitution_rules: &[FlyTermSubstitution],
    ) -> Self {
        if substitution_rules.len() == 0 {
            return self;
        }
        self.rewrite_aux(db, terms, src, substitution_rules)
    }

    fn rewrite_aux(
        self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        src: HoleSource,
        substitution_rules: &[FlyTermSubstitution],
    ) -> FlyTerm {
        assert!(substitution_rules.len() > 0);
        match self.base_term_data2(db, terms) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path,
                ty_arguments: arguments,
                ..
            } => {
                let arguments: SmallVec<[FlyTerm; 2]> = arguments.to_smallvec();
                let arguments = arguments
                    .into_iter()
                    .map(|argument| argument.rewrite_inner(db, terms, src, substitution_rules))
                    .collect();
                FlyTerm::new_ty_ontology(db, terms, path, refined_ty_path, arguments)
            }
            FlyTermData::Trait { .. } => todo!(),
            FlyTermData::Curry {
                toolchain,
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => {
                let parameter_hvar =
                    parameter_hvar.map(|v| v.rewrite_inner(db, terms, src, substitution_rules));
                let parameter_ty = parameter_ty.rewrite_inner(db, terms, src, substitution_rules);
                let return_ty = return_ty.rewrite_inner(db, terms, src, substitution_rules);
                FlyTerm::new_curry(
                    db,
                    terms,
                    toolchain,
                    curry_kind,
                    variance,
                    parameter_hvar,
                    parameter_ty,
                    return_ty,
                )
            }
            FlyTermData::Hole(_, _) => self,
            FlyTermData::Sort(_) => self,
            FlyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => {
                let mut parameter_contracted_tys = parameter_contracted_tys.to_vec();
                for parameter_contracted_ty in &mut parameter_contracted_tys {
                    *parameter_contracted_ty.ty_mut() = parameter_contracted_ty.ty().rewrite_inner(
                        db,
                        terms,
                        src,
                        substitution_rules,
                    );
                }
                let return_ty = return_ty.rewrite_inner(db, terms, src, substitution_rules);
                FlyTerm::new_ritchie_inner(
                    ritchie_kind,
                    parameter_contracted_tys,
                    return_ty,
                    db,
                    terms,
                )
                .unwrap()
            }
            FlyTermData::SymbolicVariable { .. } => todo!(),
            // todo: this is wrong
            FlyTermData::AbstractVariable { .. } => substitution_rules
                .iter()
                .copied()
                .find_map(|rule| (*rule.hvar == self).then_some(rule.substitute))
                .unwrap_or(self),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
        }
    }
}
