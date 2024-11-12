mod map;

use quote::quote;
use syn::Item;

#[proc_macro_attribute]
pub fn optimus_prime(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let item = syn::parse_macro_input!(input as Item);
    let Item::Fn(item) = item else {
        panic!("expected fn")
    };
    quote! {}.into()
}

#[proc_macro_attribute]
pub fn map(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let item = syn::parse_macro_input!(input as Item);
    let Item::Fn(item) = item else {
        panic!("expected fn")
    };
    quote! {
        #item
    }
    .into()
}
