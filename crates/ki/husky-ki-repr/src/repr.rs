mod domain_repr_guard;
pub mod source;

pub(crate) use self::domain_repr_guard::KiDomainReprGuard;

use self::source::*;
use crate::*;
use husky_entity_path::path::major_item::form::MajorFormPath;
use husky_hir_defn::defn::{major_item::form::MajorFormHirDefn, HasHirDefn};
use husky_ki::{Ki, KiArgument, KiDomain, KiOpn, KiRuntimeCompterm};
use husky_ki_repr_interface::{KiDomainReprInterface, KiReprInterface};
use husky_linket::linket::Linket;
use smallvec::{smallvec, SmallVec};

/// has more information than `Ki`
#[salsa::interned(constructor = new_inner)]
pub struct KiRepr {
    pub ki_domain_repr: KiDomainRepr,
    pub opn: KiOpn,
    #[return_ref]
    pub arguments: SmallVec<[KiArgumentRepr; 4]>,
    /// the source tells the code and the dependent variables that generates this val
    pub source: KiReprSource,
    pub caching_class: KiCachingClass,
}

impl Into<KiReprInterface> for KiRepr {
    fn into(self) -> KiReprInterface {
        unsafe { std::mem::transmute(self) }
    }
}

impl From<KiReprInterface> for KiRepr {
    fn from(ki_repr: KiReprInterface) -> Self {
        unsafe { std::mem::transmute(ki_repr) }
    }
}

#[test]
fn ki_repr_size_works() {
    assert_eq!(
        std::mem::size_of::<KiRepr>(),
        std::mem::size_of::<KiReprInterface>()
    )
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KiArgumentRepr {
    Simple(KiRepr),
    Keyed(Option<KiRepr>),
    Variadic(SmallVec<[KiRepr; 4]>),
    Branch {
        condition: Option<KiRepr>,
        stmts: SmallVec<[KiRepr; 4]>,
    },
    // `None` means no runtime constants
    RuntimeConstants(SmallVec<[KiRuntimeCompterm; 4]>),
}

#[test]
fn ki_argument_repr_size_works() {
    use husky_ki_repr_interface::KiArgumentReprInterface;

    assert_eq!(
        std::mem::size_of::<KiArgumentRepr>(),
        std::mem::size_of::<KiArgumentReprInterface>()
    )
}

impl KiRepr {
    pub fn new(
        ki_domain_repr: KiDomainRepr,
        opn: KiOpn,
        arguments: SmallVec<[KiArgumentRepr; 4]>,
        source: KiReprSource,
        db: &::salsa::Db,
    ) -> Self {
        Self::new_inner(
            db,
            ki_domain_repr,
            opn,
            arguments,
            source,
            source.caching_class(),
        )
    }

    // todo: general paths
    pub fn new_val(path: MajorFormPath, db: &::salsa::Db) -> Self {
        debug_assert_eq!(path.kind(db), husky_entity_kind::MajorFormKind::Val);
        val_ki_repr(db, path)
    }

    // todo: general paths
    pub fn new_static_var_item(path: MajorFormPath, db: &::salsa::Db) -> Self {
        static_var_item_ki_repr(db, path)
    }

    pub(crate) fn with_source(self, source: KiReprSource, db: &::salsa::Db) -> Self {
        Self::new(
            self.ki_domain_repr(db),
            self.opn(db),
            self.arguments(db).clone(),
            source,
            db,
        )
    }
}

#[salsa::tracked]
fn val_ki_repr(db: &::salsa::Db, path: MajorFormPath) -> KiRepr {
    let domain = KiDomainRepr::Omni;
    let MajorFormHirDefn::Val(hir_defn) = path.hir_defn(db).unwrap() else {
        use salsa::DebugWithDb;
        husky_print_utils::p!(path.debug(db));
        unreachable!()
    };
    let opn = match Linket::new_val(path, db) {
        Some(linket) => KiOpn::Linket(linket),
        None => KiOpn::Val(path),
    };
    let opds = smallvec![];
    let caching_class = KiCachingClass::Val;
    KiRepr::new(domain, opn, opds, KiReprSource::Val(path), db)
}

#[salsa::tracked]
fn static_var_item_ki_repr(db: &::salsa::Db, path: MajorFormPath) -> KiRepr {
    let domain = KiDomainRepr::Omni;
    let MajorFormHirDefn::StaticVar(hir_defn) = path.hir_defn(db).unwrap() else {
        unreachable!()
    };
    let opn = KiOpn::Linket(Linket::new_var(path, db));
    let opds = smallvec![];
    let caching_class = KiCachingClass::StaticVar;
    KiRepr::new(domain, opn, opds, KiReprSource::Val(path), db)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KiDomainRepr {
    /// everything
    Omni,
    /// those where the val repr of type bool is defined and equals true
    ConditionSatisfied(KiRepr),
    /// those where the val repr of type bool is defined and equals false
    ConditionNotSatisfied(KiRepr),
    /// those where the val repr of type ControlFlow<(), _> is defined and equals Continue(())
    ControlNotTransferred(KiRepr),
}

#[test]
fn ki_domain_repr_size_works() {
    assert_eq!(
        std::mem::size_of::<KiDomainRepr>(),
        std::mem::size_of::<KiDomainReprInterface>(),
    )
}

impl Into<KiDomainReprInterface> for KiDomainRepr {
    fn into(self) -> KiDomainReprInterface {
        unsafe { std::mem::transmute(self) }
    }
}

impl From<KiDomainReprInterface> for KiDomainRepr {
    fn from(ki_domain_repr: KiDomainReprInterface) -> Self {
        unsafe { std::mem::transmute(ki_domain_repr) }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum KiCachingClass {
    StaticVar,
    Val,
    Variable,
    Expr,
    Stmt,
    Condition,
    RuntimeConstant,
}

impl KiRepr {
    pub fn ki(self, db: &::salsa::Db) -> Ki {
        ki_repr_ki(db, self)
    }
}

#[salsa::tracked]
fn ki_repr_ki(db: &::salsa::Db, ki_repr: KiRepr) -> Ki {
    Ki::new(
        db,
        ki_repr.ki_domain_repr(db).ki_domain(db),
        ki_repr.opn(db),
        ki_repr
            .arguments(db)
            .iter()
            .map(|ki_repr| ki_repr.ki_argument(db))
            .collect(),
    )
}

impl KiArgumentRepr {
    fn ki_argument(&self, db: &::salsa::Db) -> KiArgument {
        match *self {
            KiArgumentRepr::Simple(ki_repr) => KiArgument::Simple(ki_repr.ki(db)),
            KiArgumentRepr::Keyed(ki_repr) => {
                KiArgument::Keyed(ki_repr.map(|ki_repr| ki_repr.ki(db)))
            }
            KiArgumentRepr::Variadic(ref ki_reprs) => {
                KiArgument::Variadic(ki_reprs.iter().map(|ki_repr| ki_repr.ki(db)).collect())
            }
            KiArgumentRepr::Branch {
                condition,
                ref stmts,
            } => KiArgument::Branch {
                condition: condition.map(|condition| condition.ki(db)),
                stmts: stmts.iter().map(|&stmt| stmt.ki(db)).collect(),
            },
            KiArgumentRepr::RuntimeConstants(ref ki_reprs) => {
                KiArgument::RuntimeCompterms(ki_reprs.clone())
            }
        }
    }
}

impl KiDomainRepr {
    pub fn ki_domain(self, db: &::salsa::Db) -> KiDomain {
        match self {
            KiDomainRepr::Omni => KiDomain::Omni,
            KiDomainRepr::ConditionSatisfied(ki_repr) => {
                KiDomain::ConditionSatisfied(ki_repr.ki(db))
            }
            KiDomainRepr::ConditionNotSatisfied(ki_repr) => {
                KiDomain::ConditionNotSatisfied(ki_repr.ki(db))
            }
            KiDomainRepr::ControlNotTransferred(ki_repr) => {
                KiDomain::ControlNotTransferred(ki_repr.ki(db))
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn val_ki_reprs(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> Vec<(MajorFormPath, KiRepr)> {
    use husky_entity_kind::MajorFormKind;
    use husky_entity_path::path::{major_item::MajorItemPath, ItemPath};
    use husky_entity_tree::helpers::paths::module_item_paths;

    module_item_paths(db, module_path)
        .iter()
        .filter_map(|&path| match path {
            ItemPath::MajorItem(MajorItemPath::Form(path)) => match path.kind(db) {
                MajorFormKind::Val => Some((path, KiRepr::new_val(path, db))),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[test]
fn val_ki_repr_works() {
    let _db = DB::default();
    DB::ast_rich_test_debug_with_db(
        val_ki_reprs,
        &AstTestConfig::new(
            "val_ki_reprs",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::VAL,
        ),
    )
}
