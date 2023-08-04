Ok(
    [
        ItemPath::MajorItem(
            MajorItemPath::Type(
                TypePath(`natural_number_game::Nat`, `Inductive`),
            ),
        ),
        ItemPath::MajorItem(
            MajorItemPath::Type(
                TypePath(`natural_number_game::OddNat`, `Structure`),
            ),
        ),
        ItemPath::MajorItem(
            MajorItemPath::Type(
                TypePath(`natural_number_game::EvenNat`, `Structure`),
            ),
        ),
        ItemPath::ImplBlock(
            ImplBlockPath::TypeImplBlock(
                TypeImplBlockPath {
                    module_path: `natural_number_game`,
                    ty_path: TypePath(`natural_number_game::Nat`, `Inductive`),
                    disambiguator: 0,
                },
            ),
        ),
    ],
)