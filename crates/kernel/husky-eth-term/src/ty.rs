use self::term::curry::EthCurry;
use super::*;
use husky_dec_ty::principal_item_path::{
    form_path_declarative_ty, trai_path_declarative_ty,
    ty_instance_constructor_path_declarative_ty, ty_ontology_path_declarative_ty,
    ty_variant::ty_variant_path_declarative_ty,
};
use husky_entity_kind::TraitItemKind;
use husky_entity_path::path::{
    major_item::{
        form::MajorFormPath,
        trai::TraitPath,
        ty::{PreludeTypePath, TypePath},
        MajorItemPath,
    },
    ty_variant::TypeVariantPath,
    PrincipalEntityPath,
};
use husky_vfs::toolchain::Toolchain;

pub trait HasType: Copy {
    fn ty(self, db: &::salsa::Db) -> EthTermResult<EthTerm>;
}

pub trait HasTypeGivenToolchain: Copy {
    fn ty(self, db: &::salsa::Db, toolchain: Toolchain) -> EthTermResult<EthTerm>;
}

pub trait HasTypeGivenDisambiguation: Copy {
    fn ty(self, db: &::salsa::Db, disambiguation: TypePathDisambiguation)
        -> EthTermResult<EthTerm>;
}

impl HasTypeGivenDisambiguation for PrincipalEntityPath {
    fn ty(
        self,
        db: &::salsa::Db,
        disambiguation: TypePathDisambiguation,
    ) -> EthTermResult<EthTerm> {
        match self {
            PrincipalEntityPath::Module(path) => {
                Ok(db.eth_term_menu(path.toolchain(db)).module_ty_ontology())
            }
            PrincipalEntityPath::MajorItem(path) => path.ty(db, disambiguation),
            PrincipalEntityPath::TypeVariant(path) => path.ty(db),
        }
    }
}

impl HasTypeGivenDisambiguation for MajorItemPath {
    fn ty(
        self,
        db: &::salsa::Db,
        disambiguation: TypePathDisambiguation,
    ) -> EthTermResult<EthTerm> {
        match self {
            MajorItemPath::Type(path) => path.ty(db, disambiguation),
            MajorItemPath::Trait(path) => path.ty(db),
            MajorItemPath::Form(path) => path.ty(db),
        }
    }
}

impl HasType for TraitPath {
    fn ty(self, db: &::salsa::Db) -> EthTermResult<EthTerm> {
        EthTerm::ty_from_dec(db, trai_path_declarative_ty(db, self)?)
    }
}

impl HasType for MajorFormPath {
    fn ty(self, db: &::salsa::Db) -> EthTermResult<EthTerm> {
        EthTerm::ty_from_dec(db, form_path_declarative_ty(db, self)?)
    }
}

impl HasTypeGivenDisambiguation for TypePath {
    fn ty(
        self,
        db: &::salsa::Db,
        disambiguation: TypePathDisambiguation,
    ) -> EthTermResult<EthTerm> {
        match disambiguation {
            TypePathDisambiguation::OntologyConstructor => {
                EthTerm::ty_from_dec(db, ty_ontology_path_declarative_ty(db, self)?)
            }
            TypePathDisambiguation::InstanceConstructor => {
                EthTerm::ty_from_dec(db, ty_instance_constructor_path_declarative_ty(db, self)?)
            }
        }
    }
}

impl HasType for TypeVariantPath {
    fn ty(self, db: &::salsa::Db) -> EthTermResult<EthTerm> {
        EthTerm::ty_from_dec(db, ty_variant_path_declarative_ty(db, self)?)
    }
}

impl HasTypeGivenToolchain for EthTerm {
    fn ty(self, _db: &::salsa::Db, _toolchain: Toolchain) -> EthTermResult<EthTerm> {
        todo!()
        // self.ty_unchecked(db)?.checked(db)
    }
}

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RawType {
    Prelude(PreludeTypePath),
    Declarative(DecTerm),
}

impl EthTerm {
    pub fn ty_unchecked(self, db: &::salsa::Db) -> EthTermResult<Either<EthTerm, PreludeTypePath>> {
        Ok(match self.raw_ty(db)? {
            RawType::Declarative(declarative_ty) => Left(EthTerm::from_dec(
                db,
                declarative_ty,
                TypeFinalDestinationExpectation::EqsSort,
            )?),
            RawType::Prelude(prelude_ty_path) => Right(prelude_ty_path),
        })
    }

    pub fn raw_ty(self, db: &::salsa::Db) -> EthTermResult<RawType> {
        Ok(match self {
            EthTerm::Literal(slf) => RawType::Prelude(slf.ty()),
            EthTerm::SymbolicVariable(slf) => RawType::Declarative(slf.ty(db).into_declarative(db)),
            EthTerm::AbstractVariable(slf) => RawType::Declarative(slf.ty(db).into_declarative(db)),
            EthTerm::ItemPath(slf) => match slf {
                ItemPathTerm::MajorForm(path) => {
                    RawType::Declarative(form_path_declarative_ty(db, path)?)
                }
                ItemPathTerm::Trait(path) => {
                    RawType::Declarative(trai_path_declarative_ty(db, path)?)
                }
                ItemPathTerm::TypeOntology(path) => {
                    RawType::Declarative(ty_ontology_path_declarative_ty(db, path)?)
                }
                ItemPathTerm::TypeInstance(path) => {
                    RawType::Declarative(ty_instance_constructor_path_declarative_ty(db, path)?)
                }
                ItemPathTerm::TypeVariant(path) => {
                    RawType::Declarative(ty_variant_path_declarative_ty(db, path)?)
                }
            },
            EthTerm::Sort(slf) => RawType::Declarative(slf.ty()?.into()),
            EthTerm::Universe(_) => RawType::Prelude(PreludeTypePath::UNIVERSE),
            EthTerm::Curry(slf) => slf.raw_ty(db),
            EthTerm::Ritchie(_) => DecTerm::Category(Sort::new(1.into())).into(),
            EthTerm::Abstraction(_) => todo!(),
            EthTerm::Application(term) => RawType::Declarative(term.declarative_ty(db)?),
            EthTerm::TypeAsTraitItem(term) => match term.trai_item_path(db).item_kind(db) {
                TraitItemKind::AssocRitchie(_) => todo!(),
                TraitItemKind::AssocType => DecTerm::Category(Sort::new(1.into())).into(), // todo: maybe consider template parameters?
                TraitItemKind::AssocVal => todo!(),
                TraitItemKind::AssocConceptual => todo!(),
                TraitItemKind::AssocCompterm => todo!(),
                TraitItemKind::MemoizedField => todo!(),
                TraitItemKind::MethodRitchie(_) => todo!(),
                TraitItemKind::AssocStaticMut => todo!(),
                TraitItemKind::AssocStaticVar => todo!(),
            },
            EthTerm::TraitConstraint(_) => todo!(),
        })
    }
}

impl EthCurry {
    fn raw_ty(self, db: &salsa::Db) -> RawType {
        let Ok(RawType::Declarative(DecTerm::Category(parameter_ty_cat))) =
            self.parameter_ty(db).raw_ty(db)
        else {
            unreachable!()
        };
        let Ok(RawType::Declarative(DecTerm::Category(return_ty_cat))) =
            self.return_ty(db).raw_ty(db)
        else {
            unreachable!()
        };
        RawType::Declarative(parameter_ty_cat.max(return_ty_cat).into())
    }
}
