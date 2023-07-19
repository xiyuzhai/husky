use super::*;

impl HasFluffyTypeMethodDispatch for EtherealTerm {
    fn ty_method_dispatch(
        self,
        engine: &mut impl FluffyTermEngine,
        expr_idx: ExprIdx,
        ident_token: IdentToken,
    ) -> FluffyTermMaybeResult<FluffyMethodDispatch> {
        let ident = ident_token.ident();
        // todo: check scope
        match self {
            EtherealTerm::EntityPath(TermEntityPath::TypeOntology(ty_path)) => {
                ethereal_ty_ontology_path_ty_method_dispatch(engine, expr_idx, ty_path, ident)
            }
            EtherealTerm::Application(ty_term) => {
                ethereal_term_application_ty_method_dispatch(engine, expr_idx, ty_term, ident)
            }
            _ => Nothing,
        }
    }
}

fn ethereal_ty_ontology_path_ty_method_dispatch(
    engine: &mut impl FluffyTermEngine,
    expr_idx: ExprIdx,
    ty_path: TypePath,
    ident: Ident,
) -> FluffyTermMaybeResult<FluffyMethodDispatch> {
    ethereal_ty_method_dispatch_aux(engine, expr_idx, ty_path, &[], ident, smallvec![])
}

fn ethereal_term_application_ty_method_dispatch(
    engine: &mut impl FluffyTermEngine,
    expr_idx: ExprIdx,
    ty_term: EtherealTermApplication,
    ident: Ident,
) -> FluffyTermMaybeResult<FluffyMethodDispatch> {
    let application_expansion = ty_term.application_expansion(engine.db());
    match application_expansion.function() {
        TermFunctionReduced::TypeOntology(ty_path) => ethereal_ty_method_dispatch_aux(
            engine,
            expr_idx,
            ty_path,
            application_expansion.arguments(engine.db()),
            ident,
            smallvec![],
        ),
        TermFunctionReduced::Trait(_) | TermFunctionReduced::Other(_) => Nothing,
    }
}

fn ethereal_ty_method_dispatch_aux(
    engine: &mut impl FluffyTermEngine,
    expr_idx: ExprIdx,
    ty_path: TypePath,
    arguments: &[EtherealTerm],
    ident: Ident,
    mut indirections: SmallVec<[FluffyDynamicDispatchIndirection; 2]>,
) -> FluffyTermMaybeResult<FluffyMethodDispatch> {
    match ty_path.refine(engine.db()) {
        Left(PreludeTypePath::Borrow(borrow_ty_path)) => match borrow_ty_path {
            PreludeBorrowTypePath::Ref => todo!(),
            PreludeBorrowTypePath::RefMut => todo!(),
            PreludeBorrowTypePath::Leash => {
                indirections.push(FluffyDynamicDispatchIndirection::Leash);
                if arguments.len() != 1 {
                    p!((&arguments).debug(engine.db()));
                    todo!()
                }
                todo!()
                // return JustOk(
                //     ethereal_ty_method_dispatch(engine, expr_idx, arguments[0], ident)?
                //         .merge(indirections),
                // );
            }
        },
        _ => (),
    }
    if let Some(signature) = ty_method_fluffy_signature(
        engine,
        expr_idx,
        ty_path,
        arguments,
        /* ad hoc */ &[],
        ident,
    )
    .into_result_option()?
    {
        return JustOk(FluffyDynamicDispatch {
            indirections,
            signature,
        });
    };
    if indirections.contains(&FluffyDynamicDispatchIndirection::Leash) {
        todo!()
    }
    // ad hoc
    // needs to consider `Deref` `DerefMut` `Carrier`
    Nothing
}