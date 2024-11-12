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
                    name: `cybertron-mini-lean-compiler`,
                    data: PackagePathSource::Local {
                        path: "../../../examples/cybertron-mini-lean-compiler",
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
                name: `cybertron-mini-lean-compiler`,
                data: PackagePathSource::Local {
                    path: "../../../examples/cybertron-mini-lean-compiler",
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
                    name: `cybertron-mini-lean-compiler`,
                    data: PackagePathSource::Local {
                        path: "../../../examples/cybertron-mini-lean-compiler",
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
                    name: `cybertron-mini-lean-compiler`,
                    data: PackagePathSource::Local {
                        path: "../../../examples/cybertron-mini-lean-compiler",
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
                    name: `cybertron-mini-lean-compiler`,
                    data: PackagePathSource::Local {
                        path: "../../../examples/cybertron-mini-lean-compiler",
                    },
                },
            ),
        },
        data: RustTranspilationPackageData::Linkets,
    },
]
```