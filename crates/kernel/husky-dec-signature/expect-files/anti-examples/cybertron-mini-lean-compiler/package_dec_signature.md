```rust
Ok(
    PackageDecSignature {
        path: PackagePath {
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
        data: PackageDecSignatureData {
            task_ty_default: None,
        },
    },
)
```