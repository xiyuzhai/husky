#[salsa::jar]
pub struct EthTermJar(
    // symbol
    crate::term::symbolic_variable::EthSymbolicVariable,
    // hvar
    crate::term::abstract_variable::EthAbstractVariable,
    // curry
    crate::term::curry::EthCurry,
    crate::term::curry::term_curry_from_dec,
    crate::term::curry::curry_parameter_count,
    // curry_parameter_count,
    // ritchie
    crate::term::ritchie::EthRitchie,
    crate::term::ritchie::ethereal_term_ritchie_from_dec_term_ritchie,
    // abstraction
    crate::term::abstraction::EthAbstraction,
    // application
    crate::term::application::EthApplication,
    crate::term::application::application_expansion_salsa,
    crate::term::application::ethereal_term_from_dec_term_application,
    crate::term::application::ethereal_term_application_declarative_ty,
    // - application reduction
    crate::term::application::reduction::reduce_eth_application,
    // - application expansion
    crate::term::application::EtherealApplicationArguments,
    // ty as trait item
    crate::term::trai_for_ty_item::EthTypeAsTraitItem,
    crate::term::trai_for_ty_item::reduce_eth_ty_as_trai_item,
    // trait constraint
    crate::term::trai_constraint::EthTraitConstraint,
    crate::menu::term_menu,
    // other
    crate::term::ethereal_term_from_application_or_ritchie_call_declarative_term,
    crate::term::ethereal_term_from_list_declarative_term,
    crate::term::ethereal_term_from_dec_term_wrapper,
    // trai
    // trai_side_trai_for_ty_impl_blocks_aux,
    // ty_side_trai_for_ty_impl_blocks_aux,
    // trai_for_type_impl_template_from_impl_block,
    // // template
    // // TemplateParameters,
    // ty_path_template_parameters,
    // context
    crate::context::EthTermContextItd,
    // fmt
    crate::fmt::item_fmt_context,
    crate::fmt::EthTermFmtContext,
    // helpers
    crate::helpers::ethereal_term_curry_toolchain,
    crate::helpers::ethereal_term_application_toolchain,
    crate::helpers::ethereal_term_ritchie_toolchain,
    crate::helpers::final_destination::application_ethereal_term_final_destination,
    crate::helpers::final_destination::curry_ethereal_term_final_destination,
);
