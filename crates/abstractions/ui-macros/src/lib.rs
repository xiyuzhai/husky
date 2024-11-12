mod settings;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(SettingsUi)]
pub fn derive_settings_ui(input: TokenStream) -> TokenStream {
    settings::derive_settings_ui(input)
}

#[proc_macro_derive(SettingSectionUi)]
pub fn derive_setting_section_ui(input: TokenStream) -> TokenStream {
    settings::section::derive_setting_section_ui(input)
}

#[proc_macro_derive(SettingSubsectionUi)]
pub fn derive_setting_subsection_ui(input: TokenStream) -> TokenStream {
    settings::subsection::derive_setting_subsection_ui(input)
}
