pub mod section;
pub mod subsection;

use crate::*;
use proc_macro2::TokenStream as TokenStream2;
use syn::{parse_macro_input, Data, DeriveInput, Fields};

pub fn derive_settings_ui(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let struct_data = match input.data {
        syn::Data::Struct(data) => data,
        _ => panic!("SettingsUi can only be derived for structs"),
    };
    let ty_ident = &input.ident;
    let process_struct_fields = process_struct_fields(&struct_data);
    let where_predicates = generate_where_predicates(&struct_data);
    let expanded = quote! {
        impl<Ui: IsUi> SettingsUi<Ui> for #ty_ident
        where
            #where_predicates
        {
            fn for_each_section(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingSectionUi<Ui>)) {
                #process_struct_fields
            }
        }
    };
    TokenStream::from(expanded)
}

fn process_struct_fields(struct_data: &syn::DataStruct) -> TokenStream2 {
    let fields = match &struct_data.fields {
        Fields::Named(fields) => &fields.named,
        _ => panic!("Only named fields are supported for SettingsUi"),
    };
    let field_uis = fields.iter().map(|field| {
        let field_name = &field.ident;
        let field_name_str = field_name.as_ref().unwrap().to_string();
        let transformed_name = transform_field_name(&field_name_str);

        quote! {
            f(#transformed_name, &mut self.#field_name);
        }
    });
    quote! {
        #(#field_uis)*
    }
}

fn transform_field_name(name: &str) -> String {
    let mut transformed = String::with_capacity(name.len());
    let mut chars = name.chars();
    if let Some(first_char) = chars.next() {
        transformed.push(first_char.to_uppercase().next().unwrap());
    }
    for c in chars {
        if c == '_' {
            transformed.push(' ');
        } else {
            transformed.push(c);
        }
    }
    transformed
}

fn generate_where_predicates(struct_data: &syn::DataStruct) -> TokenStream2 {
    let fields = match &struct_data.fields {
        Fields::Named(fields) => &fields.named,
        _ => panic!("Only named fields are supported for SettingsUi"),
    };
    let where_predicates = fields.iter().map(|field| {
        let field_type = &field.ty;
        quote! { #field_type: SettingSectionUi<Ui> }
    });
    quote! { #(#where_predicates,)* }
}
