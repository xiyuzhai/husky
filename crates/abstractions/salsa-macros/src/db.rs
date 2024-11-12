use std::collections::{BTreeMap, BTreeSet};

use syn::Token;

pub(crate) fn db(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let args = syn::parse_macro_input!(args as Args);
    let input = syn::parse_macro_input!(input as syn::ItemStruct);
    let ident = &input.ident;
    let vis = &input.vis;
    check_jar_paths(args.jar_paths.iter());
    let initialization: proc_macro2::TokenStream = initialization(args);

    quote! {
        #vis struct #ident(::salsa::Db);

        impl std::ops::Deref for #ident {
            type Target = ::salsa::Db;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl std::ops::DerefMut for #ident {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }

        impl Default for #ident {
            fn default() -> Self {
                Self(::salsa::Db::new(|jars, routes| {
                    *jars = ::salsa::jar::Jars::default();
                    #initialization
                }))
            }
        }

        impl ::salsa::snapshot::SnapshotClone for #ident {
            fn snapshot_clone(&self) -> Self {
                Self(self.0.snapshot_clone())
            }
        }
    }
    .into()
}

fn initialization(args: Args) -> proc_macro2::TokenStream {
    if !args.jar_paths.is_empty() {
        args.jar_paths
            .iter()
            .map(|jar_path| {
                quote! {
                    jars.initialize_jar::<#jar_path>(routes);
                }
            })
            .collect()
    } else {
        todo!()
    }
}

fn check_jar_paths<'a>(jar_paths: impl Iterator<Item = &'a syn::Path>) {
    let jar_idents: Vec<String> = jar_paths
        .map(|jar_path| jar_path.segments.last().unwrap().ident.to_string())
        .collect();
    let jar_tree = decode_jar_tree();
    for jar_ident in &jar_idents {
        use convert_case::Case;
        use convert_case::Casing;

        assert!(jar_ident.ends_with("Jar"));
        if jar_ident == "Jar" {
            continue;
        }
        let jar_package_name = if jar_ident.starts_with("Lx") {
            format!(
                "latex-{}",
                jar_ident[2..]
                    .split("Jar")
                    .next()
                    .unwrap()
                    .to_case(Case::Kebab)
            )
            .replace("-type", "-ty")
        } else if jar_ident.starts_with("Vd") {
            format!(
                "visored-{}",
                jar_ident[2..]
                    .split("Jar")
                    .next()
                    .unwrap()
                    .to_case(Case::Kebab)
            )
            .replace("-type", "-ty")
        } else if jar_ident.starts_with("Ln") {
            format!(
                "lean-{}",
                jar_ident[2..]
                    .split("Jar")
                    .next()
                    .unwrap()
                    .to_case(Case::Kebab)
            )
            .replace("-type", "-ty")
        } else if jar_ident.starts_with("Ie") {
            format!(
                "isabelle-{}",
                jar_ident[2..]
                    .split("Jar")
                    .next()
                    .unwrap()
                    .to_case(Case::Kebab)
            )
            .replace("-type", "-ty")
        } else {
            format!(
                "husky-{}",
                jar_ident.split("Jar").next().unwrap().to_case(Case::Kebab)
            )
            .replace("-type", "-ty")
        };
        let Some(deps) = jar_tree.get(&jar_package_name) else {
            panic!("{jar_package_name} is not present in jar tree. Make sure jar tree is updated.");
        };
        for dep in deps {
            let dep_jar_ident = if dep.starts_with("husky-") {
                let kebab = dep.split("husky-").last().unwrap();
                format!("{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else if dep.starts_with("latex-") {
                let kebab = dep.split("latex-").last().unwrap();
                format!("Lx{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else if dep.starts_with("visored-") {
                let kebab = dep.split("visored-").last().unwrap();
                format!("Vd{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else if dep.starts_with("lean-") {
                let kebab = dep.split("lean-").last().unwrap();
                format!("Ln{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else if dep.starts_with("isabelle-") {
                let kebab = dep.split("isabelle-").last().unwrap();
                format!("Ie{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else if dep.starts_with("rocq-") {
                let kebab = dep.split("rocq-").last().unwrap();
                format!("Rq{}Jar", kebab.to_case(Case::Pascal)).replace("Ty", "Type")
            } else {
                todo!()
            };
            assert!(
                jar_idents.contains(&dep_jar_ident),
                "expect `{dep_jar_ident}` to be included as a dependency for `{jar_ident}`"
            )
        }
    }

    fn decode_jar_tree() -> BTreeMap<String, BTreeSet<String>> {
        let cargo_manifest_dir: std::path::PathBuf =
            std::env::var("CARGO_MANIFEST_DIR").unwrap().into();
        let path = cargo_manifest_dir
            .join("../../utils/husky-jar-utils/expect-files/husky_lang_jar_tree.json");
        assert!(path.exists(), "expect {path:?} to exist");
        let text = std::fs::read_to_string(path).unwrap();
        serde_json::from_str(&text).unwrap()
    }
}

pub struct Args {
    jar_paths: syn::punctuated::Punctuated<syn::Path, Token![,]>,
}

impl syn::parse::Parse for Args {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        Ok(Self {
            jar_paths: syn::punctuated::Punctuated::parse_terminated(input)?,
        })
    }
}
