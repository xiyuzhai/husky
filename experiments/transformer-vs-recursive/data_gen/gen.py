import json
import gzip
import os
import pdb
from pathlib import Path

from data_gen.utils import rnd_codes_parallel

def write_data(dataset_filepath, split, data):
    compressed_filepath = f"{dataset_filepath}_{split}.json.gz"
    with gzip.open(compressed_filepath, 'wt', encoding='utf-8') as file:
        json.dump(data, file)
    print(f"Data written and compressed to {compressed_filepath}")

def main():
    dir_path = Path(os.path.join(os.environ["DATA_ROOT"],
                                 "mini-husky/basic"))
    os.makedirs(dir_path, exist_ok=True)

    params = [
        (100000, 10, 5, 5, 3, 0.2, 0.5),
        (200000, 20, 5, 5, 3, 0.2, 0.5),
        (200000, 20, 5, 5, 5, 0.2, 0.5),
        (300000, 40, 5, 5, 5, 0.2, 0.5),
        (300000, 40, 5, 5, 10, 0.2, 0.5),
        (400000, 80, 5, 5, 10, 0.2, 0.5),
        (400000, 80, 5, 5, 20, 0.2, 0.5),
    ]

    files_to_keep = []

    for n, max_fns, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate in params:
        dataset_filename = dir_path / f"dataset-n{n}-f{max_fns}-a{max_args_per_fn}-c{max_calls_per_fn}-d{min_dist}-v{use_var_rate:.2f}-e{error_rate:.2f}"
        files_to_keep.append(f"{dataset_filename}.json.gz")

        # Generate the random codes
        train = rnd_codes_parallel(True, int(n * 0.8), max_fns, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate, workers=16)
        eval = rnd_codes_parallel(False, int(n * 0.2), max_fns, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate, workers=16)

        print("train:", train[0]["text"])
        print("eval:", eval[0]["text"])

        # Write and compress the file
        write_data(dataset_filename, "train", train)
        write_data(dataset_filename, "eval", eval)

    # Clear other files in the folder
    for entry in dir_path.iterdir():
        if entry.is_file() and entry.suffixes == ['.json', '.gz', ".msgpack"] and str(entry) not in files_to_keep:
            entry.unlink()
            print(f"Removed old file: {entry}")

if __name__ == "__main__":
    main()
