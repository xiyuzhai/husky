mod interned;
mod memo;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::*;

#[proc_macro_attribute]
pub fn interned(attr: TokenStream, item: TokenStream) -> TokenStream {
    interned::interned(attr, item)
}

#[proc_macro_attribute]
pub fn memo(attr: TokenStream, item: TokenStream) -> TokenStream {
    memo::memo(attr, item)
}
