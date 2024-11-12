use super::*;

#[derive(Debug, Deserialize, PartialEq, Eq)]
pub struct MayuriConfig {}

#[derive(Debug, Deserialize, PartialEq, Eq)]
pub struct SrcConfig {
    pub path: PathBuf,
}

#[cfg(test)]
mod tests {
    use super::*;
    use toml;

    #[test]
    fn config_works() {
        let toml_str = r#"
            "#;

        assert_eq!(MayuriConfig {}, toml::from_str(toml_str).unwrap());
    }
}
