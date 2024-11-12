use crate::*;
use std::str::FromStr;

impl FromStr for Makefile {
    type Err = Box<dyn std::error::Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Check for proper indentation
        check_makefile_indentation(&s)?;

        // Parse the Makefile
        let makefile: makefile_lossless::Makefile = s.parse()?;
        Ok(Self(makefile))
    }
}

/// Checks if the given Makefile content contains any lines starting with spaces.
///
/// # Arguments
///
/// * `content` - A string slice containing the Makefile content.
///
/// # Returns
///
/// `Ok(())` if no lines start with spaces, otherwise an `Err` with a descriptive message.
fn check_makefile_indentation(content: &str) -> Result<(), Box<dyn std::error::Error>> {
    if content.lines().any(|line| line.starts_with(' ')) {
        Err("Makefile contains lines starting with spaces. Use tabs for indentation.".into())
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, expect_file};

    #[test]
    fn parse_makefile_example() {
        // Example Makefile content as a string
        let makefile_content = r#"
.PHONY: build test clean

build:
	cargo build --release

test:
	cargo test

clean:
	cargo clean
"#;

        // Parse the Makefile content
        let mf: Makefile = makefile_content.parse().unwrap();

        // Convert the Makefile back to a string
        let makefile_string = mf.to_string();

        // Use expect_test to compare the parsed Makefile string
        expect![[r#"

            .PHONY: build test clean

            build:
            	cargo build --release

            test:
            	cargo test

            clean:
            	cargo clean
        "#]]
        .assert_eq(&makefile_string);

        // Use expect_test to compare with the original content
        expect![[r#"
            .PHONY: build test clean

            build:
            	cargo build --release

            test:
            	cargo test

            clean:
            	cargo clean"#]]
        .assert_eq(makefile_content.trim());

        // Use expect_test to check the rules in the Makefile
        let rules_string = mf
            .rules()
            .map(|r| r.targets().collect::<Vec<String>>().join(" "))
            .collect::<Vec<_>>()
            .join(", ");

        expect![[r#".PHONY, build, test, clean"#]].assert_eq(&rules_string);
    }

    #[test]
    #[ignore]
    fn parse_makefile_example2() {
        // Example Makefile content as a string
        let makefile_content = r#"
.PHONY: build test clean
build:
	cargo build --release
test:
	cargo test
clean:
	cargo clean
"#;

        // Parse the Makefile content
        let mf: Makefile = makefile_content.parse().unwrap();

        // Convert the Makefile back to a string
        let makefile_string = mf.to_string();

        // Use expect_test to compare the parsed Makefile string
        expect![[r#"

            .PHONY: build test clean
            build:
            	cargo build --release
            test:
            	cargo test
            clean:
            	cargo clean
        "#]]
        .assert_eq(&makefile_string);

        // Use expect_test to compare with the original content
        expect![[r#"
            .PHONY: build test clean
            build:
            	cargo build --release
            test:
            	cargo test
            clean:
            	cargo clean"#]]
        .assert_eq(makefile_content.trim());

        // Use expect_test to check the rules in the Makefile
        let rules_string = mf
            .rules()
            .map(|r| r.targets().collect::<Vec<String>>().join(" "))
            .collect::<Vec<_>>()
            .join(", ");

        expect![[r#".PHONY, build, test, clean"#]].assert_eq(&rules_string);
    }

    #[test]
    #[ignore]
    fn parse_makefile_example3() {
        // Example Makefile content as a string
        let makefile_content = r#"
.PHONY: build test clean
build:
	cargo build --release
test:
	cargo test
clean:
	cargo clean"#;

        // Parse the Makefile content
        let mf: Makefile = makefile_content.parse().unwrap();

        // Convert the Makefile back to a string
        let makefile_string = mf.to_string();

        // Use expect_test to compare the parsed Makefile string
        expect![[r#"

            .PHONY: build test clean
            build:
            	cargo build --release
            test:
            	cargo test
            clean:
            	cargo clean
        "#]]
        .assert_eq(&makefile_string);

        // Use expect_test to compare with the original content
        expect![[r#"
            .PHONY: build test clean
            build:
            	cargo build --release
            test:
            	cargo test
            clean:
            	cargo clean"#]]
        .assert_eq(makefile_content.trim());

        // Use expect_test to check the rules in the Makefile
        let rules_string = mf
            .rules()
            .map(|r| r.targets().collect::<Vec<String>>().join(" "))
            .collect::<Vec<_>>()
            .join(", ");

        expect![[r#".PHONY, build, test, clean"#]].assert_eq(&rules_string);
    }

    #[test]
    #[ignore]
    fn parse_makefile_example4() {
        // Example Makefile content as a string
        let makefile_content = "\nclean:\n\tcargo clean\n";

        // Parse the Makefile content
        let mf: makefile_lossless::Makefile = makefile_content.parse().unwrap();
        // Example Makefile content as a string
        let makefile_content = "\nclean:\n\tcargo clean";

        // Parse the Makefile content
        let mf: makefile_lossless::Makefile = makefile_content.parse().unwrap();
    }
}
