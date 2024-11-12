use crate::*;

// todo: make the durability SUPER_LOW using macros
// #[salsa::input]
// pub struct Script {
//     pub source: ScriptSource,
//     #[return_ref]
//     pub data: String,
// }

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash, Debug)]
pub struct Script(salsa::Id);

impl Script {
    pub fn new(__db: &::salsa::Db, source: ScriptSource, data: String) -> Self {
        let (__jar, __runtime) = __db.jar::<crate::Jar>();
        let __ingredients =
            <crate::Jar as salsa::storage::HasIngredientsFor<Script>>::ingredient(__jar);
        let __id = __ingredients.2.new_input(__runtime);
        __ingredients
            .0
            .store_new(__runtime, __id, source, salsa::Durability::LOW);
        __ingredients
            .1
            .store_new(__runtime, __id, data, salsa::Durability::LOW);
        __id
    }
    pub fn source<'db>(self, __db: &'db ::salsa::Db) -> ScriptSource {
        let (__jar, __runtime) = __db.jar::<crate::Jar>();
        let __ingredients =
            <crate::Jar as salsa::storage::HasIngredientsFor<Script>>::ingredient(__jar);
        __ingredients.0.fetch(__runtime, self).clone()
    }
    pub fn data<'db>(self, __db: &'db ::salsa::Db) -> &'db String {
        let (__jar, __runtime) = __db.jar::<crate::Jar>();
        let __ingredients =
            <crate::Jar as salsa::storage::HasIngredientsFor<Script>>::ingredient(__jar);
        __ingredients.1.fetch(__runtime, self)
    }
    pub fn set_source<'db>(
        self,
        __db: &'db mut ::salsa::Db,
    ) -> salsa::setter::Setter<'db, Script, ScriptSource> {
        let (__jar, __runtime) = __db.jar_mut::<crate::Jar>();
        let __ingredients =
            <crate::Jar as salsa::storage::HasIngredientsFor<Script>>::ingredient_mut(__jar);
        salsa::setter::Setter::new(
            __runtime,
            self,
            salsa::Durability::SUPER_LOW,
            &mut __ingredients.0,
        )
    }

    pub fn set_data<'db>(
        self,
        __db: &'db mut ::salsa::Db,
    ) -> salsa::setter::Setter<'db, Script, String> {
        let (__jar, __runtime) = __db.jar_mut::<crate::Jar>();
        let __ingredients =
            <crate::Jar as salsa::storage::HasIngredientsFor<Script>>::ingredient_mut(__jar);
        salsa::setter::Setter::new(
            __runtime,
            self,
            salsa::Durability::SUPER_LOW,
            &mut __ingredients.1,
        )
    }
}
impl salsa::storage::IngredientsFor for Script {
    type Jar = crate::Jar;
    type Ingredients = (
        salsa::input_field::InputFieldIngredient<Script, ScriptSource>,
        salsa::input_field::InputFieldIngredient<Script, String>,
        salsa::input::InputIngredient<Script>,
    );
    fn create_ingredients(routes: &mut salsa::routes::Routes) -> Self::Ingredients {
        (
            {
                let index = routes.push(
                    |jars| {
                        let jar = jars.jar::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient(jar);
                        &ingredients.0
                    },
                    |jars| {
                        let jar = jars.jar_mut::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient_mut(jar);
                        &mut ingredients.0
                    },
                );
                salsa::input_field::InputFieldIngredient::new(index, "source")
            },
            {
                let index = routes.push(
                    |jars| {
                        let jar = jars.jar::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient(jar);
                        &ingredients.1
                    },
                    |jars| {
                        let jar = jars.jar_mut::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient_mut(jar);
                        &mut ingredients.1
                    },
                );
                salsa::input_field::InputFieldIngredient::new(index, "data")
            },
            {
                let index = routes.push(
                    |jars| {
                        let jar = jars.jar::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient(jar);
                        &ingredients.2
                    },
                    |jars| {
                        let jar = jars.jar_mut::<Self::Jar>();
                        let ingredients =
                            <_ as salsa::storage::HasIngredientsFor<Self>>::ingredient_mut(jar);
                        &mut ingredients.2
                    },
                );
                salsa::input::InputIngredient::new(index, "Script")
            },
        )
    }
}
impl salsa::AsId for Script {
    fn as_id(self) -> salsa::Id {
        self.0
    }
    fn from_id(id: salsa::Id) -> Self {
        Script(id)
    }
}
impl ::salsa::DebugWithDb for Script {
    fn debug_fmt_with_db(
        &self,
        f: &mut ::std::fmt::Formatter<'_>,
        _db: &::salsa::Db,
    ) -> ::std::fmt::Result {
        use ::salsa::fmt::{WithFmtContext, WithFmtContextTest};
        WithFmtContextTest(self).with_fmt_context(
            || {
                #[allow(unused_imports)]
                use ::salsa::debug::helper::Fallback;
                #[allow(warnings)]
                let mut debug_struct = &mut f.debug_struct("Script");
                debug_struct = debug_struct.field(
                    "source",
                    &::salsa::debug::helper::SalsaDebug::<ScriptSource>::salsa_debug(
                        #[allow(clippy::needless_borrow)]
                        &self.source(_db),
                        _db,
                    ),
                );
                debug_struct = debug_struct.field(
                    "data",
                    &::salsa::debug::helper::SalsaDebug::<String>::salsa_debug(
                        #[allow(clippy::needless_borrow)]
                        &self.data(_db),
                        _db,
                    ),
                );
                debug_struct.finish()
            },
            _db,
        )
    }
}
impl salsa::salsa_struct::SalsaStructInDb for Script {
    fn register_dependent_fn(_db: &::salsa::Db, _index: salsa::routes::IngredientIndex) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScriptSource {
    Snippet { toolchain: Toolchain },
    Follower { followed: Script },
    Repl { module_path: ModulePath },
}

impl Script {
    #[cfg(feature = "test_helpers")]
    pub fn new_dev_snippet(data: impl Into<String>, db: &::salsa::Db) -> Self {
        let toolchain = db.dev_toolchain().unwrap();
        Self::new(db, ScriptSource::Snippet { toolchain }, data.into())
    }

    pub fn toolchain(self, db: &::salsa::Db) -> Toolchain {
        chunk_toolchain(db, self)
    }

    pub fn module_path(self, db: &::salsa::Db) -> ScriptModulePath {
        ScriptModulePath::new(self, db)
    }
}

#[salsa::tracked]
fn chunk_toolchain(db: &::salsa::Db, script: Script) -> Toolchain {
    match script.source(db) {
        ScriptSource::Snippet { toolchain } => toolchain,
        ScriptSource::Follower { followed } => followed.toolchain(db),
        ScriptSource::Repl { module_path } => module_path.toolchain(db),
    }
}
