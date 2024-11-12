```rust
Ok(
    [
        PackagePath {
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
        PackagePath {
            toolchain: Toolchain {
                data: ToolchainData::Local {
                    library_path: "../../../library",
                },
            },
            name: `core`,
            data: PackagePathSource::Library,
        },
        PackagePath {
            toolchain: Toolchain {
                data: ToolchainData::Local {
                    library_path: "../../../library",
                },
            },
            name: `cybertron-mini-lean-tokens`,
            data: PackagePathSource::Registry {
                registry_path: RegistryPath(
                    "../../../.corgi/../registry",
                ),
                version: Version {
                    major: 0,
                    minor: 1,
                    patch: 0,
                },
            },
        },
    ],
)
```