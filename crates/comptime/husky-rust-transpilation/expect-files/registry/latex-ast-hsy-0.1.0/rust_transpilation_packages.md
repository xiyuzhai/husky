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
                    name: `latex-ast-hsy`,
                    data: PackagePathSource::Local {
                        path: "../../../registry/latex-ast-hsy-0.1.0",
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
                name: `latex-ast-hsy`,
                data: PackagePathSource::Local {
                    path: "../../../registry/latex-ast-hsy-0.1.0",
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
                    name: `latex-ast-hsy`,
                    data: PackagePathSource::Local {
                        path: "../../../registry/latex-ast-hsy-0.1.0",
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
                    name: `latex-ast-hsy`,
                    data: PackagePathSource::Local {
                        path: "../../../registry/latex-ast-hsy-0.1.0",
                    },
                },
            ),
        },
        data: RustTranspilationPackageData::Linkets,
    },
]
```