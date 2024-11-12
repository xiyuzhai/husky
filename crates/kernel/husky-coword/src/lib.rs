mod ident;
pub mod jar;
mod kebab;
mod label;
mod menu;
mod style;
#[cfg(test)]
mod tests;

pub use self::ident::*;
pub use self::kebab::*;
pub use self::label::*;
pub use self::menu::*;
pub use self::style::*;

use self::jar::CowordJar as Jar;
use salsa::Db;

/// the underlying type for all word like types used in representing source code
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash, Debug)]
pub struct Coword(salsa::Id);

#[doc = r" Internal struct used for interned item"]
#[derive(Eq, PartialEq, Hash, Clone)]
pub struct __CowordData {
    data: String,
}

impl salsa::storage::IngredientsFor for Coword {
    type Jar = Jar;
    type Ingredients = salsa::interned::InternedIngredient<Coword, __CowordData>;
    fn create_ingredients(routes: &mut salsa::routes::Routes) -> Self::Ingredients {
        let index = routes.push(
            |jars| {
                let jar = jars.jar::<Self::Jar>();
                <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient(jar)
            },
            |jars| {
                let jar = jars.jar_mut::<Self::Jar>();
                <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient_mut(jar)
            },
        );
        salsa::interned::InternedIngredient::new(index, "Word")
    }
}
impl salsa::AsId for Coword {
    fn as_id(self) -> salsa::Id {
        self.0
    }
    fn from_id(id: salsa::Id) -> Self {
        Coword(id)
    }
}

impl Coword {
    pub fn data<'db>(self, db: &'db Db) -> &'db str {
        let (jar, runtime) = db.jar::<Jar>();
        let ingredients = <Jar as salsa::storage::HasIngredientsFor<Coword>>::ingredient(jar);
        &ingredients.data(runtime, self).data
    }
    pub fn new(db: &::salsa::Db, data: String) -> Self {
        let (jar, runtime) = db.jar::<Jar>();
        let ingredients = <Jar as salsa::storage::HasIngredientsFor<Coword>>::ingredient(jar);
        ingredients.intern(runtime, __CowordData { data })
    }
}

impl salsa::salsa_struct::SalsaStructInDb for Coword {
    fn register_dependent_fn(_db: &::salsa::Db, _index: salsa::routes::IngredientIndex) {}
}

impl ::salsa::DebugWithDb for Coword {
    fn debug_fmt_with_db(
        &self,
        f: &mut ::std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> ::std::fmt::Result {
        f.debug_tuple("Coword").field(&self.data(db)).finish()
    }
}

impl std::borrow::Borrow<str> for __CowordData {
    fn borrow(&self) -> &str {
        &self.data
    }
}

impl<'a> From<&'a str> for __CowordData {
    fn from(value: &'a str) -> Self {
        Self { data: value.into() }
    }
}

impl Coword {
    pub fn from_owned(db: &::salsa::Db, data: String) -> Self {
        let (jar, runtime) = db.jar::<Jar>();
        let ingredients = <Jar as salsa::storage::HasIngredientsFor<Coword>>::ingredient(jar);
        ingredients.intern(runtime, __CowordData { data })
    }

    pub fn from_ref(db: &::salsa::Db, data: &str) -> Self {
        let (jar, runtime) = db.jar::<Jar>();
        let ingredients = <Jar as salsa::storage::HasIngredientsFor<Coword>>::ingredient(jar);
        ingredients.intern_borrowed(runtime, data)
    }
}
