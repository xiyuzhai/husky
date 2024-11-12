use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::Path;

pub fn set_up_gitignore(root: &Path, append: bool) -> io::Result<()> {
    let gitignore_path = root.join(".gitignore");
    let required_patterns = vec!["env", "experiments/.local", "tests/.local"];

    if gitignore_path.exists() {
        let file = fs::File::open(&gitignore_path)?;
        let reader = BufReader::new(file);
        let existing_lines: Vec<String> = reader.lines().collect::<io::Result<_>>()?;

        let missing_patterns: Vec<&str> = required_patterns
            .iter()
            .filter(|&pattern| !existing_lines.iter().any(|line| line.trim() == *pattern))
            .map(|&s| s)
            .collect();

        if !missing_patterns.is_empty() {
            if !append {
                panic!(".gitignore file already exists and append is set to false");
            }

            let mut file = OpenOptions::new().append(true).open(&gitignore_path)?;
            writeln!(file, "\n# Added by Mayuri")?;
            for pattern in missing_patterns {
                writeln!(file, "{}", pattern)?;
            }
        }
    } else {
        let gitignore_content = required_patterns.join("\n");
        fs::write(&gitignore_path, gitignore_content)?;
    }

    Ok(())
}
