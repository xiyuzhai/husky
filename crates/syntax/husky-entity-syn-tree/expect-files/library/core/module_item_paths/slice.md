Ok(
    [
        ItemPath::MajorItem(
            MajorItemPath::Type(
                TypePath(`core::slice::Slice`, `Extern`),
            ),
        ),
        ItemPath::MajorItem(
            MajorItemPath::Type(
                TypePath(`core::slice::CyclicSliceLeashed`, `Extern`),
            ),
        ),
        ItemPath::ImplBlock(
            ImplBlockPath::TypeImplBlock(
                TypeImplBlockPath {
                    module_path: `core::slice`,
                    ty_path: TypePath(`core::slice::CyclicSliceLeashed`, `Extern`),
                    disambiguator: 0,
                },
            ),
        ),
        ItemPath::AssociatedItem(
            AssociatedItemPath::TypeItem(
                TypeItemPath {
                    impl_block: TypeImplBlockPath {
                        module_path: `core::slice`,
                        ty_path: TypePath(`core::slice::CyclicSliceLeashed`, `Extern`),
                        disambiguator: 0,
                    },
                    ident: `ilen`,
                    item_kind: MethodFn,
                },
            ),
        ),
        ItemPath::AssociatedItem(
            AssociatedItemPath::TypeItem(
                TypeItemPath {
                    impl_block: TypeImplBlockPath {
                        module_path: `core::slice`,
                        ty_path: TypePath(`core::slice::CyclicSliceLeashed`, `Extern`),
                        disambiguator: 0,
                    },
                    ident: `first`,
                    item_kind: MethodFn,
                },
            ),
        ),
        ItemPath::AssociatedItem(
            AssociatedItemPath::TypeItem(
                TypeItemPath {
                    impl_block: TypeImplBlockPath {
                        module_path: `core::slice`,
                        ty_path: TypePath(`core::slice::CyclicSliceLeashed`, `Extern`),
                        disambiguator: 0,
                    },
                    ident: `last`,
                    item_kind: MethodFn,
                },
            ),
        ),
    ],
)