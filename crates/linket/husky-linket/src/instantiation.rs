use husky_hir_ty::{
    instantiation::{HirInstantiation, HirTermSymbolicVariableResolution},
    HirTemplateVariable, HirTemplateVariableClass,
};
use husky_javelin::{
    instantiation::{JavInstantiation, JavTermSymbolResolution},
    template_argument::JavTemplateArgument,
};

use smallvec::*;
use vec_like::{SmallVecMap, SmallVecPairMap};

use crate::{
    context::LinTypeContext,
    template_argument::{constant::LinConstant, qual::LinQual, ty::LinType, LinTemplateArgument},
};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct LinInstantiation {
    context: LinTypeContext,
    symbol_resolutions: SmallVecPairMap<HirTemplateVariable, LinTermSymbolResolution, 4>,
    separator: Option<u8>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LinTermSymbolResolution {
    Explicit(LinTemplateArgument),
    SelfLifetime,
    SelfQual(LinQual),
}

impl LinInstantiation {
    pub fn new_empty(is_associated: bool) -> Self {
        LinInstantiation {
            // todo: is this correct?
            context: LinTypeContext::new_empty(),
            symbol_resolutions: Default::default(),
            separator: is_associated.then_some(0),
        }
    }

    /// this is quite casual. We don't have any complications like nondeterminism for comptime vars,
    /// as compared with symbol resolutions, by design.
    pub(crate) fn new_empty_for_comptime_var_overrides() -> Self {
        Self::new_empty(false)
    }

    #[track_caller]
    pub(crate) fn from_hir(
        hir_instantiation: &HirInstantiation,
        lin_instantiation: &LinInstantiation,
        db: &::salsa::Db,
    ) -> LinInstantiation {
        let symbol_resolutions =
            SmallVecMap::from_iter(hir_instantiation.symbol_map().iter().filter_map(
                |&(symbol, resolution)| {
                    match symbol {
                        HirTemplateVariable::Compterm(symbol)
                            if symbol.index(db).class() == HirTemplateVariableClass::Poly =>
                        {
                            return None
                        }
                        _ => (),
                    }
                    Some((
                        symbol,
                        LinTermSymbolResolution::from_hir(resolution, lin_instantiation, db),
                    ))
                },
            ));
        let separator = hir_instantiation.separator();
        LinInstantiation {
            context: LinTypeContext::from_hir(hir_instantiation.context(), lin_instantiation, db),
            symbol_resolutions,
            separator,
        }
    }
}

impl LinInstantiation {
    pub fn is_empty(&self) -> bool {
        self.context.comptime_var_overrides().is_empty() && self.symbol_resolutions.is_empty()
    }

    #[track_caller]
    pub(crate) fn resolve(&self, symbol: HirTemplateVariable) -> LinTermSymbolResolution {
        self.symbol_resolutions[symbol].1
    }

    pub fn places(&self) -> SmallVec<[(HirTemplateVariable, LinTermSymbolResolution); 2]> {
        self.symbol_resolutions
            .iter()
            .filter_map(|&(symbol, resolution)| match resolution {
                LinTermSymbolResolution::Explicit(LinTemplateArgument::Qual(_))
                | LinTermSymbolResolution::SelfQual(_) => Some((symbol, resolution)),
                LinTermSymbolResolution::Explicit(_) | LinTermSymbolResolution::SelfLifetime => {
                    None
                }
            })
            .collect()
    }

    pub fn symbol_resolutions(&self) -> &[(HirTemplateVariable, LinTermSymbolResolution)] {
        self.symbol_resolutions.as_ref()
    }

    pub fn separator(&self) -> Option<u8> {
        self.separator
    }

    pub fn context(&self) -> &LinTypeContext {
        &self.context
    }
}

impl LinInstantiation {
    /// a nondeterminstic map basically
    pub(crate) fn from_jav(
        jav_instantiation: &JavInstantiation,
        db: &::salsa::Db,
    ) -> SmallVec<[Self; 4]> {
        let mut lin_instantiations = smallvec![];
        Self::from_jav_aux(
            jav_instantiation,
            LinInstantiation {
                context: LinTypeContext::from_jav(jav_instantiation.context(), db),
                symbol_resolutions: Default::default(),
                separator: jav_instantiation.separator,
            },
            &mut lin_instantiations,
            db,
        );
        lin_instantiations
    }

    fn from_jav_aux(
        jav_instantiation: &JavInstantiation,
        prefix: LinInstantiation,
        lin_instantiations: &mut SmallVec<[Self; 4]>,
        db: &::salsa::Db,
    ) {
        if prefix.symbol_resolutions.len() == jav_instantiation.symbol_resolutions.len() {
            lin_instantiations.push(prefix);
            return;
        }
        let (symbol, javelin_resolution) =
            jav_instantiation.symbol_resolutions.data()[prefix.symbol_resolutions.len()];
        let linket_resolutions = LinTermSymbolResolution::from_jav(javelin_resolution, &prefix, db);
        for linket_resolution in linket_resolutions {
            let mut prefix = prefix.clone();
            unsafe {
                prefix
                    .symbol_resolutions
                    .insert_new_unchecked((symbol, linket_resolution))
            };
            Self::from_jav_aux(jav_instantiation, prefix, lin_instantiations, db)
        }
    }
}

impl LinTermSymbolResolution {
    fn from_jav(
        javelin_resolution: JavTermSymbolResolution,
        lin_instantiation: &LinInstantiation,
        db: &::salsa::Db,
    ) -> SmallVec<[Self; 4]> {
        match javelin_resolution {
            JavTermSymbolResolution::Explicit(arg) => match arg {
                JavTemplateArgument::Vacant => todo!(),
                JavTemplateArgument::Type(javelin_ty) => {
                    smallvec![LinTermSymbolResolution::Explicit(
                        LinTemplateArgument::Type(LinType::from_jav(
                            javelin_ty,
                            lin_instantiation,
                            db
                        ))
                    )]
                }
                JavTemplateArgument::Constant(constant) => {
                    smallvec![LinTermSymbolResolution::Explicit(
                        LinTemplateArgument::Constant(LinConstant(constant))
                    )]
                }
                JavTemplateArgument::Lifetime => todo!(),
                JavTemplateArgument::Place => todo!(),
            },
            JavTermSymbolResolution::SelfLifetime => {
                smallvec![LinTermSymbolResolution::SelfLifetime]
            }
            JavTermSymbolResolution::SelfPlace => {
                smallvec![
                    LinTermSymbolResolution::SelfQual(LinQual::Ref),
                    LinTermSymbolResolution::SelfQual(LinQual::RefMut),
                ]
            }
        }
    }

    fn from_hir(
        resolution: HirTermSymbolicVariableResolution,
        instantiation: &LinInstantiation,
        db: &salsa::Db,
    ) -> LinTermSymbolResolution {
        match resolution {
            HirTermSymbolicVariableResolution::Explicit(arg) => LinTermSymbolResolution::Explicit(
                LinTemplateArgument::from_hir(arg, instantiation, db),
            ),
            HirTermSymbolicVariableResolution::SelfLifetime => {
                LinTermSymbolResolution::SelfLifetime
            }
            HirTermSymbolicVariableResolution::SelfContractedQuary(contracted_quary) => {
                LinTermSymbolResolution::SelfQual(LinQual::from_hir(contracted_quary))
            }
        }
    }
}

pub trait LinInstantiate {
    type Output;

    fn lin_instantiate(
        self,
        lin_instantiation: &LinInstantiation,
        db: &::salsa::Db,
    ) -> Self::Output;
}