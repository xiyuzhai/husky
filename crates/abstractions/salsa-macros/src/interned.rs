use crate::salsa_struct::{SalsaStruct, SalsaStructKind};
use proc_macro2::TokenStream;

// #[salsa::interned(jar = Jar0, data = TyData0)]
// #[derive(Eq, PartialEq, Hash, Debug, Clone)]
// struct Ty0 {
//    field1: Type1,
//    #[id(ref)] field2: Type2,
//    ...
// }

pub(crate) fn interned(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match SalsaStruct::new(SalsaStructKind::Interned, args, input)
        .and_then(|el| InternedStruct(el).generate_interned())
    {
        Ok(s) => s.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

struct InternedStruct(SalsaStruct<Self>);

impl std::ops::Deref for InternedStruct {
    type Target = SalsaStruct<Self>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl crate::options::AllowedOptions for InternedStruct {
    const RETURN_REF: bool = false;

    const SPECIFY: bool = false;

    const NO_EQ: bool = false;

    const SINGLETON: bool = false;

    const JAR: bool = true;

    const DATA: bool = true;

    const DB: bool = true;

    const RECOVERY_FN: bool = false;

    const LRU: bool = false;

    const CONSTRUCTOR: bool = true;

    const OVERRIDE_DEBUG: bool = true;
}

impl InternedStruct {
    fn generate_interned(&self) -> syn::Result<TokenStream> {
        self.validate_interned()?;
        let id_struct = self.id_struct(SalsaStructKind::Interned);
        let data_struct = self.data_struct();
        let ingredients_for_impl = self.ingredients_for_impl();
        let as_id_impl = self.as_id_impl();
        let named_fields_impl = self.inherent_impl_for_named_fields();
        let salsa_struct_in_db_impl = self.salsa_struct_in_db_impl();
        let as_debug_with_db_impl = (!self.override_debug()).then(|| self.as_debug_with_db_impl());
        Ok(quote! {
            #id_struct
            #data_struct
            #ingredients_for_impl
            #as_id_impl
            #named_fields_impl
            #salsa_struct_in_db_impl
            #as_debug_with_db_impl
        })
    }

    fn validate_interned(&self) -> syn::Result<()> {
        self.disallow_id_fields("interned")?;
        Ok(())
    }

    /// If this is an interned struct, then generate methods to access each field,
    /// as well as a `new` method.
    fn inherent_impl_for_named_fields(&self) -> syn::ItemImpl {
        let constructor_visibility = self.constructor_visibility();
        let id_ident = self.id_ident();
        let jar_ty = self.jar_ty();

        let field_getters: Vec<syn::ImplItemFn> = self
            .all_fields()
            .map(|field| {
                let field_name = field.name();
                let field_ty = field.ty();
                let field_vis = field.vis();
                let field_get_name = field.get_name();
                if field.is_clone_field() {
                    parse_quote! {
                        #field_vis fn #field_get_name(self, db: &::salsa::Db,) -> #field_ty {
                            let (jar, runtime) = db.jar::<#jar_ty>();
                            let ingredients = <#jar_ty as salsa::storage::HasIngredientsFor< #id_ident >>::ingredient(jar);
                            std::clone::Clone::clone(&ingredients.data(runtime, self).#field_name)
                        }
                    }
                } else {
                    parse_quote! {
                        #field_vis fn #field_get_name<'db>(self, db: &'db ::salsa::Db) -> &'db #field_ty {
                            let (jar, runtime) = db.jar::<#jar_ty>();
                            let ingredients = <#jar_ty as salsa::storage::HasIngredientsFor< #id_ident >>::ingredient(jar);
                            &ingredients.data(runtime, self).#field_name
                        }
                    }
                }
            })
            .collect();

        let field_names = self.all_field_names();
        let field_tys = self.all_field_tys();
        let data_ident = self.data_ident();
        let constructor_name = self.constructor_name();
        let new_method: syn::ImplItemFn = parse_quote! {
            #constructor_visibility fn #constructor_name(
                db: &::salsa::Db,
                #(#field_names: #field_tys,)*
            ) -> Self {
                let (jar, runtime) = db.jar::<#jar_ty>();
                let ingredients = <#jar_ty as salsa::storage::HasIngredientsFor< #id_ident >>::ingredient(jar);
                ingredients.intern(runtime, #data_ident {
                    #(#field_names,)*
                })
            }
        };

        parse_quote! {
            impl #id_ident {
                #(#field_getters)*

                #new_method
            }
        }
    }

    /// Generates an impl of `salsa::storage::IngredientsFor`.
    ///
    /// For a memoized type, the only ingredient is an `InternedIngredient`.
    fn ingredients_for_impl(&self) -> syn::ItemImpl {
        let id_ident = self.id_ident();
        let debug_name = crate::literal(id_ident);
        let jar_ty = self.jar_ty();
        let data_ident = self.data_ident();
        parse_quote! {
            impl salsa::storage::IngredientsFor for #id_ident {
                type Jar = #jar_ty;
                type Ingredients = salsa::interned::InternedIngredient<#id_ident, #data_ident>;

                fn create_ingredients(
                    routes: &mut salsa::routes::Routes,
                ) -> Self::Ingredients
                {
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
                    salsa::interned::InternedIngredient::new(index, #debug_name)
                }
            }
        }
    }

    /// Implementation of `SalsaStructInDb`.
    fn salsa_struct_in_db_impl(&self) -> syn::ItemImpl {
        let ident = self.id_ident();
        let _jar_ty = self.jar_ty();
        parse_quote! {
            impl salsa::salsa_struct::SalsaStructInDb for #ident
            {
                fn register_dependent_fn(_db: &::salsa::Db, _index: salsa::routes::IngredientIndex) {
                    // Do nothing here, at least for now.
                    // If/when we add ability to delete inputs, this would become relevant.
                }
            }
        }
    }
}
