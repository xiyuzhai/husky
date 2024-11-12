#!/usr/bin/env python

import os
import sys
import shutil
import re
import subprocess
from colorama import Fore, Style, init

# Initialize colorama
init(autoreset=True)

# Usage: python rename_rust_package.py <old_package_name> <new_package_name>


def rename_rust_package(old_package_name, new_package_name):
    # Find all directories containing the old package name and a Cargo.toml file
    package_dirs = []
    for root, dirs, files in os.walk("."):
        for dir_name in dirs:
            if old_package_name in dir_name:
                potential_package_dir = os.path.join(root, dir_name)
                if "Cargo.toml" in os.listdir(potential_package_dir):
                    package_dirs.append(potential_package_dir)

    if not package_dirs:
        print(
            f"Error: No Rust package directories containing '{old_package_name}' found in the workspace."
        )
        sys.exit(1)

    for package_dir in package_dirs:
        # Rename the package directory
        new_dir_name = package_dir.replace(old_package_name, new_package_name)
        shutil.move(package_dir, new_dir_name)
        print(f"Renamed directory: {package_dir} -> {new_dir_name}")

    # Update references in Cargo.toml files
    for root, _, files in os.walk("."):
        for file_name in files:
            if file_name == "Cargo.toml":
                update_file_content(
                    os.path.join(root, file_name), old_package_name, new_package_name
                )

    # Update references in Rust source files (.rs)
    for root, _, files in os.walk("."):
        for file_name in files:
            if file_name.endswith(".rs"):
                update_file_content(
                    os.path.join(root, file_name), old_package_name, new_package_name
                )

    print(
        f"Package references updated from '{old_package_name}' to '{new_package_name}' successfully."
    )


def update_file_content(file_path, old_name, new_name):
    with open(file_path, "r") as file:
        content = file.read()

    if file_path.endswith(".toml"):
        # For Cargo.toml files, do a simple replacement
        if old_name in content:
            content = content.replace(old_name, new_name)
            with open(file_path, "w") as file:
                file.write(content)
            print(f"Updated Cargo.toml file: {file_path}")

    elif file_path.endswith(".rs"):
        # For Rust files, handle both hyphenated and underscore versions
        if old_name in content or old_name.replace("-", "_") in content:
            # Replace hyphenated version
            content = content.replace(old_name, new_name)
            # Replace underscore version
            content = re.sub(
                rf'\b{re.escape(old_name).replace("-", "_")}\b',
                new_name.replace("-", "_"),
                content,
            )
            with open(file_path, "w") as file:
                file.write(content)
            print(f"Updated Rust file: {file_path}")


def is_git_repo_clean():
    try:
        # Check for uncommitted changes
        subprocess.run(["git", "diff", "--quiet", "--exit-code"], check=True)

        # Check for staged changes
        subprocess.run(
            ["git", "diff", "--staged", "--quiet", "--exit-code"], check=True
        )

        # Check for untracked files
        result = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            capture_output=True,
            text=True,
            check=True,
        )
        if result.stdout.strip():
            return False

        return True
    except subprocess.CalledProcessError:
        return False


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(
            f"{Fore.YELLOW}Usage: python rename_rust_package.py <old_package_name> <new_package_name>{Style.RESET_ALL}"
        )
        sys.exit(1)

    if not is_git_repo_clean():
        print(
            f"{Fore.RED}Error: Git repository is not clean. Please commit or stash your changes.{Style.RESET_ALL}"
        )
        sys.exit(1)

    old_package_name = sys.argv[1]
    new_package_name = sys.argv[2]
    rename_rust_package(old_package_name, new_package_name)
