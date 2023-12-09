mod memoized_field;
mod val_item;

use proc_macro::TokenStream;
use quote::quote;
use syn::{Ident, ItemFn, ReturnType, Signature};

#[proc_macro_attribute]
pub fn val_item(args: TokenStream, input: TokenStream) -> TokenStream {
    val_item::val_item_aux(input, false)
}

#[proc_macro_attribute]
pub fn val_item_return_ref(args: TokenStream, input: TokenStream) -> TokenStream {
    val_item::val_item_aux(input, true)
}

#[proc_macro_attribute]
pub fn memoized_field(args: TokenStream, input: TokenStream) -> TokenStream {
    memoized_field::memoized_field_aux(input, false)
}

#[proc_macro_attribute]
pub fn memoized_field_return_ref(args: TokenStream, input: TokenStream) -> TokenStream {
    memoized_field::memoized_field_aux(input, true)
}