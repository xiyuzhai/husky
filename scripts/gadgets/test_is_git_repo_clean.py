#!/usr/bin/env python
import subprocess


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
    result = is_git_repo_clean()
    print(f"Is the Git repository clean? {'Yes' if result else 'No'}")
