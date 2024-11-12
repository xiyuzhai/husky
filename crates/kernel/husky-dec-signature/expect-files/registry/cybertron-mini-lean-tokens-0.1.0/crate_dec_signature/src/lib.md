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
                    name: `cybertron-mini-lean-tokens`,
                    data: PackagePathSource::Local {
                        path: "../../../registry/cybertron-mini-lean-tokens-0.1.0",
                    },
                },
                kind: Lib,
            },
            default_const_excludes: None,
        },
    ),
)
```