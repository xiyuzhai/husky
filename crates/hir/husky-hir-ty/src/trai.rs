use crate::*;
use husky_entity_path::path::major_item::trai::TraitPath;
use husky_eth_signature::signature::HasEthTemplate;
use husky_eth_term::term::{
    application::{EthApplication, TermFunctionReduced},
    symbolic_variable::EthTermVariableIndexImpl,
    EthTerm,
};
use husky_term_prelude::ItemPathTerm;

#[salsa::interned(jar = HirTypeJar)]
pub struct HirTrait {
    pub trai_path: TraitPath,
    /// phantom arguments are ignored
    #[return_ref]
    pub template_arguments: HirTemplateArguments,
}

impl HirTrait {
    pub fn from_eth(trai_term: EthTerm, db: &::salsa::Db) -> Self {
        match trai_term {
            EthTerm::Literal(_) => todo!(),
            EthTerm::SymbolicVariable(_) => todo!(),
            EthTerm::AbstractVariable(_) => todo!(),
            EthTerm::ItemPath(path) => match path {
                ItemPathTerm::MajorForm(_) => todo!(),
                ItemPathTerm::Trait(trai_path) => Self::new(db, trai_path, smallvec![]),
                ItemPathTerm::TypeOntology(_) => todo!(),
                ItemPathTerm::TypeInstance(_) => todo!(),
                ItemPathTerm::TypeVariant(_) => todo!(),
            },
            EthTerm::Sort(_) => todo!(),
            EthTerm::Universe(_) => todo!(),
            EthTerm::Curry(_) => todo!(),
            EthTerm::Ritchie(_) => todo!(),
            EthTerm::Abstraction(_) => todo!(),
            EthTerm::Application(trai_term) => hir_trai_from_eth_term_application(db, trai_term),
            EthTerm::TypeAsTraitItem(_) => todo!(),
            EthTerm::TraitConstraint(_) => todo!(),
        }
    }
}

#[salsa::tracked(jar = HirTypeJar)]
fn hir_trai_from_eth_term_application(db: &::salsa::Db, trai_term: EthApplication) -> HirTrait {
    let application_expansion = trai_term.application_expansion(db);
    match application_expansion.function() {
        TermFunctionReduced::TypeOntology(_) => todo!(),
        TermFunctionReduced::Trait(trai_path) => {
            let ty_eth_template = trai_path.eth_template(db).expect("ok");
            // todo: turn the following into utils
            let template_parameters = ty_eth_template.template_parameters(db);
            // filter out phantoms
            let template_arguments = std::iter::zip(
                template_parameters.iter(),
                application_expansion.arguments(db).iter().copied(),
            )
            .filter_map(|(param, arg)| match param.variable().index(db).inner() {
                EthTermVariableIndexImpl::ExplicitLifetime {
                    attrs: _,
                    variance: _,
                    disambiguator: _,
                } => todo!(),
                EthTermVariableIndexImpl::ExplicitPlace {
                    attrs: _,
                    variance: _,
                    disambiguator: _,
                } => todo!(),
                EthTermVariableIndexImpl::Type { attrs, .. } => (!attrs.phantom())
                    .then(|| HirTemplateArgument::Type(HirType::from_eth(arg, db).unwrap())),
                EthTermVariableIndexImpl::Prop { .. } => None,
                EthTermVariableIndexImpl::ConstPathLeading { .. }
                | EthTermVariableIndexImpl::ConstOther { .. } => todo!(),
                EthTermVariableIndexImpl::EphemPathLeading { .. }
                | EthTermVariableIndexImpl::EphemOther { .. }
                | EthTermVariableIndexImpl::SelfType
                | EthTermVariableIndexImpl::SelfValue
                | EthTermVariableIndexImpl::SelfLifetime
                | EthTermVariableIndexImpl::SelfPlace => unreachable!(),
            })
            .collect();
            HirTrait::new(db, trai_path, template_arguments).into()
        }
        TermFunctionReduced::TypeVar(_) => todo!(),
        TermFunctionReduced::Other(_) => todo!(),
    }
}
