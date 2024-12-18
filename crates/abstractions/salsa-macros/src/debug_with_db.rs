mod derive_enum;
mod derive_struct;

use self::derive_enum::*;
use self::derive_struct::*;
use crate::options::Options;
use husky_proc_macro_utils::generics_with_debug_with_db;
use husky_proc_macro_utils::self_ty;
use proc_macro2::Span;
use syn::{spanned::Spanned, Item};
use syn::{Ident, ItemStruct};

type Args = Options<DeriveDebugWithDb>;

pub(crate) fn debug_with_db(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let _options = syn::parse_macro_input!(args as Args);
    let mut item = syn::parse_macro_input!(input as Item);
    let impl_debug_with_db = match item {
        Item::Enum(ref mut item) => enum_debug_with_db_impl(item),
        Item::Struct(ref mut item) => struct_debug_with_db_impl(item),
        _ => panic!("expect enum or struct for `derive_debug_with_db`"),
    };
    quote! {
        #item

        #impl_debug_with_db
    }
    .into()
}

struct DeriveDebugWithDb;

impl crate::options::AllowedOptions for DeriveDebugWithDb {
    const RETURN_REF: bool = false;

    const SPECIFY: bool = false;

    const NO_EQ: bool = false;

    const SINGLETON: bool = false;

    const JAR: bool = false;

    const DATA: bool = false;

    const DB: bool = false;

    const RECOVERY_FN: bool = false;

    const LRU: bool = false;

    const CONSTRUCTOR: bool = false;

    const OVERRIDE_DEBUG: bool = false;
}
