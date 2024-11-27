use crate::*;
use husky_entity_path::path::{
    major_item::MajorItemPath, submodule::SubmoduleItemPath, ty_variant::TypeVariantPath,
    PrincipalEntityPath,
};
use husky_regional_token::RegionalTokenIdx;

#[salsa::tracked]
pub struct UseSymbol {
    pub original_symbol: EntitySymbol,
    pub path: PrincipalEntityPath,
    pub visibility: Scope,
    pub ast_idx: AstIdx,
    pub use_expr_idx: UseExprIdx,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum EntitySymbol {
    CrateRoot {
        root_module_path: ModulePath,
    },
    RootSelfModule {
        module_path: ModulePath,
    },
    RootSuperModule {
        current_module_path: ModulePath,
        super_module_path: ModulePath,
    },
    UniversalPrelude {
        item_path: PrincipalEntityPath,
    },
    PackageDependencyOrSelfLib {
        item_path: PrincipalEntityPath,
    },
    Submodule {
        submodule_item_path: SubmoduleItemPath,
    },
    MajorItem {
        major_item_path: MajorItemPath,
    },
    TypeVariant {
        ty_variant_path: TypeVariantPath,
    },
    ParentSuper(ParentSuperSymbol),
    Use(UseSymbol),
}

impl EntitySymbol {
    pub(crate) fn super_symbol(self, db: &::salsa::Db) -> EntityTreeResult<Self> {
        let parent_super_module_path = match self.principal_entity_path(db) {
            PrincipalEntityPath::Module(parent_super_module_path) => parent_super_module_path,
            PrincipalEntityPath::MajorItem(_) | PrincipalEntityPath::TypeVariant(_) => {
                Err(OriginalEntityTreeError::CanOnlyUseParentSuperForModulePath)?
            }
        };
        Ok(ParentSuperSymbol::new(db, self, parent_super_module_path).into())
    }
}

#[salsa::tracked]
pub struct ParentSuperSymbol {
    pub parent_symbol: EntitySymbol,
    pub parent_super_module_path: ModulePath,
}

impl EntitySymbol {
    pub(crate) fn from_node(db: &::salsa::Db, node: &ItemSynNode) -> Option<Self> {
        match node {
            ItemSynNode::Submodule(node) => Some(EntitySymbol::Submodule {
                submodule_item_path: node.unambiguous_item_path(db)?,
            }),
            ItemSynNode::MajorItem(node) => Some(EntitySymbol::MajorItem {
                major_item_path: node.unambiguous_item_path(db)?,
            }),
            ItemSynNode::TypeVariant(_) | ItemSynNode::ImplBlock(_) | ItemSynNode::Attr(_) => {
                unreachable!("these nodes shouldn't have been created at this stage")
            }
        }
    }
}

impl EntitySymbol {
    pub fn principal_entity_path(self, db: &::salsa::Db) -> PrincipalEntityPath {
        match self {
            EntitySymbol::CrateRoot { root_module_path } => root_module_path.into(),
            EntitySymbol::RootSelfModule { module_path } => module_path.into(),
            EntitySymbol::RootSuperModule {
                super_module_path, ..
            } => super_module_path.into(),
            EntitySymbol::UniversalPrelude { item_path }
            | EntitySymbol::PackageDependencyOrSelfLib { item_path } => item_path.into(),
            EntitySymbol::Submodule {
                submodule_item_path: submodule_path,
                ..
            } => submodule_path.self_module_path(db).into(),
            EntitySymbol::MajorItem {
                major_item_path: module_item_path,
                ..
            } => module_item_path.into(),
            // symbol.path(db).into(),
            EntitySymbol::Use(symbol) => symbol.path(db).into(),
            EntitySymbol::TypeVariant { ty_variant_path } => ty_variant_path.into(),
            EntitySymbol::ParentSuper(symbol) => symbol.parent_super_module_path(db).into(),
        }
    }
}

// can only see module symbols
#[derive(Debug, Clone, Copy)]
pub struct ModuleSymbolContext<'a> {
    crate_prelude: CratePrelude<'a>,
    module_symbols: EntitySymbolTableRef<'a>,
}

impl<'a> ModuleSymbolContext<'a> {
    pub fn new(crate_prelude: CratePrelude<'a>, module_symbols: EntitySymbolTableRef<'a>) -> Self {
        Self {
            crate_prelude,
            module_symbols,
        }
    }

    pub fn new_default(db: &'a ::salsa::Db, crate_path: CratePath) -> PreludeResult<Self> {
        Ok(Self {
            crate_prelude: CratePrelude::new(db, crate_path)?,
            module_symbols: Default::default(),
        })
    }

    pub fn resolve_ident(
        &self,
        db: &'a ::salsa::Db,
        reference_module_path: ModulePath,
        _token_idx: RegionalTokenIdx,
        ident: Ident,
    ) -> Option<EntitySymbol> {
        self.module_symbols
            .resolve_ident(db, reference_module_path.into(), ident)
            .or_else(|| {
                self.crate_prelude
                    .resolve_ident(db, reference_module_path, ident)
            })
    }
}

pub(crate) fn module_symbol_context<'a>(
    db: &'a ::salsa::Db,
    module_path: ModulePath,
) -> EntityTreeResult<ModuleSymbolContext<'a>> {
    let item_tree_sheet = db.item_syn_tree_sheet(module_path);
    Ok(ModuleSymbolContext {
        crate_prelude: CratePrelude::new(db, module_path.crate_path(db))?,
        module_symbols: item_tree_sheet.module_symbols().into(),
    })
}
