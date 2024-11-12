```rust
Ok(
    CrateDecSignature::Lib(
        LibCrateDecSignature {
            crate_path: CratePath {
                package_path: PackagePath {
                    toolchain: Toolchain {
                        data: ToolchainData::Local {
                            library_path: "../../../library",
                        },
                    },
                    name: `cybertron-mini-lean-compiler`,
                    data: PackagePathSource::Local {
                        path: "../../../examples/cybertron-mini-lean-compiler",
                    },
                },
                kind: Lib,
            },
            default_const_excludes: None,
        },
    ),
)
```