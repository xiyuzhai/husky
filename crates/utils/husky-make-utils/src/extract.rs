use crate::*;
use std::borrow::Cow;
use std::collections::HashSet;
use std::fs;
use std::path::Path;

/// Extracts specified rules from a Makefile and returns them as a new Makefile string.
///
/// # Arguments
///
/// * `makefile_path` - A path to the Makefile to read from.
/// * `required_rules` - A set of rule names that must be included in the output.
///
/// # Returns
///
/// A `Result` containing the extracted Makefile as a `String` if successful,
/// or an `io::Error` if file reading fails or a `ParseError` if Makefile parsing fails.
///
/// # Errors
///
/// This function will return an error if:
/// * The file cannot be read
/// * The Makefile content cannot be parsed
/// * Any of the required rules are not found in the Makefile
pub fn extract_makefile_rules(
    makefile_path: impl AsRef<Path>,
    required_rules: impl IntoIterator<Item = String>,
) -> Result<String, Box<dyn std::error::Error>> {
    // Read the Makefile content
    let makefile_content = fs::read_to_string(makefile_path)?;

    // Use the new function to extract rules from content
    extract_makefile_rules_from_content(&makefile_content, required_rules)
}

pub fn extract_makefile_rules_from_content(
    makefile_content: &str,
    required_rules: impl IntoIterator<Item = String>,
) -> Result<String, Box<dyn std::error::Error>> {
    // Parse the Makefile
    let makefile: Makefile = makefile_content.parse()?;
    let mut extracted_content = String::new();

    for required_rule in required_rules {
        let mut rule_found = false;
        for rule in makefile.rules() {
            let rule_name = rule.targets().next().unwrap();
            if rule_name == required_rule {
                extracted_content.push_str(&rule.to_string());
                rule_found = true;
                break;
            }
        }
        if !rule_found {
            return Err(format!("Missing required rule: {}", required_rule).into());
        }
    }

    // All required rules were found and added
    Ok(extracted_content)
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn test_extract_makefile_rules() {
        let makefile_content = r#"
.PHONY: build test clean
build:
	cargo build --release

test:
	cargo test

clean:
	cargo clean

unused:
	echo "This rule should not be extracted"
"#;

        // Define the required rules
        let required_rules = vec!["build".to_string(), "test".to_string()];

        // Extract the rules
        let result = extract_makefile_rules_from_content(makefile_content, required_rules);

        // Check the result
        assert!(
            result.is_ok(),
            "Failed to extract Makefile rules: {:?}",
            result.err()
        );
        let extracted_makefile = result.unwrap();

        // Use expect_test to compare the extracted Makefile
        expect![[r#"
            build:
            	cargo build --release

            test:
            	cargo test"#]]
        .assert_eq(&extracted_makefile.trim());

        // Test with missing rule
        let required_rules = vec!["build".to_string(), "missing_rule".to_string()];

        let result = extract_makefile_rules_from_content(makefile_content, required_rules);

        // Check that the function returns an error for missing rules
        assert!(result.is_err());
        let error_message = result.unwrap_err().to_string();
        expect!["Missing required rule: missing_rule"].assert_eq(&error_message);
    }
}
