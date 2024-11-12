use cargo::core::Summary;
use husky_cargo_utils::metadata::workspace_package_summaries;
use husky_path_utils::{HuskyLangDevPaths, PathBuf};
use husky_print_utils::p;
use pathdiff::diff_paths;
use serde::{de::IntoDeserializer, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub fn husky_lang_packages() -> Vec<PackageSummary> {
    let dev_paths = HuskyLangDevPaths::new();
    workspace_package_summaries(dev_paths.root())
        .into_iter()
        .map(|summary| PackageSummary::new(summary, &dev_paths))
        .collect()
}

#[derive(Debug, Serialize)]
pub struct PackageSummary {
    name: String,
    relative_path: String,
    dependencies: Vec<String>,
}

impl PackageSummary {
    fn new(summary: Summary, dev_paths: &HuskyLangDevPaths) -> Self {
        let url = summary.source_id().url().to_string();
        let dev_root = dev_paths.root();
        assert!(url.starts_with("file://"));
        let path: PathBuf = url.trim_start_matches("file://").into();
        assert!(path.exists());
        let relative_path = diff_paths(path, dev_root)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string();
        Self {
            name: summary.name().to_string(),
            relative_path,
            dependencies: summary
                .dependencies()
                .iter()
                .filter_map(|dep| {
                    (dep.package_name() != summary.name()).then(|| dep.package_name().to_string())
                })
                .collect(),
        }
    }
}

#[test]
fn husky_lang_packages_works() {
    let packages = husky_lang_packages();
    let dev_paths = HuskyLangDevPaths::new();
    let dir = dev_paths
        .cargo_manifest_dir()
        .map(|p| p.to_owned())
        .unwrap_or("temp".into())
        .join("expect-files");
    std::fs::create_dir_all(&dir).expect("failed_to_create_dir_all");
    let expected = expect_test::expect_file![dir.join("husky_lang_packages.txt")];
    expected.assert_eq(&format!("{packages:#?}"));
}

pub fn husky_lang_jar_packages() -> Vec<JarPackageSummary> {
    let dev_paths = HuskyLangDevPaths::new();
    let package_summaries: Vec<_> = husky_lang_packages()
        .into_iter()
        .filter(|package| {
            (!package.relative_path.starts_with("crates/abstraction"))
                && dev_paths
                    .root()
                    .join(&package.relative_path)
                    .join("src/jar.rs")
                    .exists()
        })
        .collect();
    let package_names: BTreeSet<String> = package_summaries
        .iter()
        .map(|package| package.name.clone())
        .collect();
    package_summaries
        .into_iter()
        .map(|package| JarPackageSummary::new(package, &package_names))
        .collect()
}

#[derive(Debug, Serialize)]
pub struct JarPackageSummary {
    name: String,
    dependencies: Vec<String>,
}

impl JarPackageSummary {
    fn new(summary: PackageSummary, package_names: &BTreeSet<String>) -> Self {
        Self {
            name: summary.name,
            dependencies: summary
                .dependencies
                .into_iter()
                .filter(|dep| package_names.contains(dep))
                .collect(),
        }
    }
}

#[test]
fn husky_lang_jar_packages_works() {
    let jar_packages = husky_lang_jar_packages();
    let dev_paths = HuskyLangDevPaths::new();
    let dir = dev_paths
        .cargo_manifest_dir()
        .map(|p| p.to_owned())
        .unwrap_or("temp".into())
        .join("expect-files");
    std::fs::create_dir_all(&dir).expect("failed_to_create_dir_all");
    let expected = expect_test::expect_file![dir.join("husky_lang_jar_packages.txt")];
    expected.assert_eq(&format!("{jar_packages:#?}"));
}

struct JarTreeBuilder<'a> {
    jar_package_summaries: &'a [JarPackageSummary],
    dependencies_table: BTreeMap<String, BTreeSet<String>>,
}

impl<'a> JarTreeBuilder<'a> {
    fn new(jar_package_summaries: &'a [JarPackageSummary]) -> Self {
        Self {
            jar_package_summaries,
            dependencies_table: Default::default(),
        }
    }
}

impl<'a> JarTreeBuilder<'a> {
    fn build_all(&mut self) {
        for summary in self.jar_package_summaries {
            self.build(&summary);
        }
    }

    fn build(&mut self, summary: &'a JarPackageSummary) {
        if self.dependencies_table.contains_key(&summary.name) {
            return;
        }
        let mut dependencies: BTreeSet<String> = Default::default();
        for dep in &summary.dependencies {
            if dep != &summary.name {
                dependencies.insert(dep.clone());
                let dep_summary = self
                    .jar_package_summaries
                    .iter()
                    .find(|summary| &summary.name == dep)
                    .unwrap();
                self.build(dep_summary);
                dependencies.extend(self.dependencies_table[dep].clone())
            }
        }
        self.dependencies_table
            .insert(summary.name.clone(), dependencies);
    }

    fn finish(self) -> BTreeMap<String, BTreeSet<String>> {
        self.dependencies_table
    }
}

pub fn husky_lang_jar_tree() -> BTreeMap<String, BTreeSet<String>> {
    let jar_packages = husky_lang_jar_packages();
    let mut builder = JarTreeBuilder::new(&jar_packages);
    builder.build_all();
    builder.finish()
}

#[test]
fn husky_lang_jar_tree_works() {
    let jar_tree = husky_lang_jar_tree();
    let dev_paths = HuskyLangDevPaths::new();
    let dir = dev_paths
        .cargo_manifest_dir()
        .map(|p| p.to_owned())
        .unwrap_or("temp".into())
        .join("expect-files");
    std::fs::create_dir_all(&dir).expect("failed_to_create_dir_all");
    expect_test::expect_file![dir.join("husky_lang_jar_tree.txt")]
        .assert_eq(&format!("{jar_tree:#?}"));
    expect_test::expect_file![dir.join("husky_lang_jar_tree.json")]
        .assert_eq(&serde_json::to_string_pretty(&jar_tree).unwrap());
}

pub fn husky_lang_jar_tree_trimmed() -> BTreeMap<String, BTreeSet<String>> {
    let jar_tree = husky_lang_jar_tree();
    jar_tree
        .iter()
        .map(|(name, deps)| {
            let mut deps_trimmed = deps.clone();
            for dep in deps {
                for dep_dep in &jar_tree[dep] {
                    deps_trimmed.remove(dep_dep);
                }
            }
            (name.clone(), deps_trimmed)
        })
        .collect()
}

#[test]
fn husky_lang_jar_tree_trimmed_works() {
    let jar_tree_trimmed = husky_lang_jar_tree_trimmed();
    let dev_paths = HuskyLangDevPaths::new();
    let dir = dev_paths
        .cargo_manifest_dir()
        .map(|p| p.to_owned())
        .unwrap_or("temp".into())
        .join("expect-files");
    std::fs::create_dir_all(&dir).expect("failed_to_create_dir_all");
    expect_test::expect_file![dir.join("husky_lang_jar_tree_trimmed.txt")]
        .assert_eq(&format!("{jar_tree_trimmed:#?}"));
    expect_test::expect_file![dir.join("husky_lang_jar_tree_trimmed.json")]
        .assert_eq(&serde_json::to_string_pretty(&jar_tree_trimmed).unwrap());
}
