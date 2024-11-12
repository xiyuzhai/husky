use cybertron_mini_husky_compiler::rnd::basic::{rnd_codes, TokenInfo};
use rmp_serde::{Deserializer, Serializer};
use serde::Serialize;
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;
use std::path::PathBuf;

fn preview_data_strings(data: &Vec<(Vec<String>, Vec<TokenInfo>)>) {
    'outer: for (strings, _tokens) in data {
        for s in strings {
            print!("{} ", s);
        }
        break 'outer;
    }
    println!();
}

fn main() {
    let dir = PathBuf::from("data/mini-husky/basic");
    assert!(dir.exists());

    // Predefined sets of parameters
    let params = vec![
        (1000000, 10, 3, 0.2, 0.5),
        // (100000, 20, 5, 0.2, 0.5),
        // (100000, 40, 10, 0.2, 0.5),
        // (100000, 80, 20, 0.2, 0.5),
    ];

    // Keep track of files we're going to write
    let mut files_to_keep = Vec::new();

    for (n, max_fns, min_dist, use_var_rate, error_rate) in &params {
        let dataset_filename = dir.join(format!(
            "dataset-n{}-f{}-d{}-v{:.2}-e{:.2}.msgpack",
            n, max_fns, min_dist, use_var_rate, error_rate
        ));
        files_to_keep.push(dataset_filename.clone());

        // Generate the random codes
        let data = rnd_codes(*n, *max_fns, *min_dist, *use_var_rate, *error_rate);

        preview_data_strings(&data);

        // Write to the file
        let mut file = fs::File::create(&dataset_filename).expect("Unable to create file");
        write_data(&dataset_filename, &data).expect("Unable to write data");
    }

    // Clear other files in the folder
    for entry in fs::read_dir(&dir).expect("Unable to read directory") {
        if let Ok(entry) = entry {
            let path = entry.path();
            if path.is_file()
                && path.extension().unwrap_or_default() == "msgpack"
                && !files_to_keep.contains(&path)
            {
                fs::remove_file(&path).expect("Unable to remove file");
                println!("Removed old file: {:?}", path);
            }
        }
    }
}

fn write_data<T: serde::Serialize>(dataset_filepath: &Path, data: &T) -> io::Result<()> {
    let header = [
        "ast_kind",
        "symbol_resolution",
        "expected_type",
        "actual_type",
    ];

    // Open a file in write mode
    let mut file = fs::File::create(dataset_filepath)?;

    // Serialize and write the header first
    header.serialize(&mut Serializer::new(&mut file));

    // Serialize and write your actual data
    data.serialize(&mut Serializer::new(&mut file));

    println!("Data written to {:?}", dataset_filepath);

    Ok(())
}
