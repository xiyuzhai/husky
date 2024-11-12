```rust
[
    RustTranspilationPackage {
        target_path: LinktimeTargetPath {
            data: LinktimeTargetPathData::Package(
                PackagePath {
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
            ),
        },
        data: RustTranspilationPackageData::Source {
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
        },
    },
    RustTranspilationPackage {
        target_path: LinktimeTargetPath {
            data: LinktimeTargetPathData::Package(
                PackagePath {
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
            ),
        },
        data: RustTranspilationPackageData::Source {
            package_path: PackagePath {
                toolchain: Toolchain {
                    data: ToolchainData::Local {
                        library_path: "../../../library",
                    },
                },
                name: `core`,
                data: PackagePathSource::Library,
            },
        },
    },
    RustTranspilationPackage {
        target_path: LinktimeTargetPath {
            data: LinktimeTargetPathData::Package(
                PackagePath {
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
            ),
        },
        data: RustTranspilationPackageData::Linkets,
    },
]
```