```rust
Ok(
    PackageSynopsis::Lib {
        lib_crate_path: CratePath {
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
        task_crate_path: None,
    },
)
```