# Development Pitfalls

This document summarizes common pitfalls encountered during development.

## VSCode Behaviors

- **Avoid using `println!()` in release code** for VSCode extensions, as this can lead to unexpected behaviors.
- If the user mistakenly uses `lib.rs` instead of `lib.hsy`, ensure that errors are reported in `Corgi.toml`.

## Missing `libtorch`

- This issue might be related to environment variables set in the fish shell. Consider using the `-gx` flag.

## Error: Undefined Symbol `c10::detail::torchCheckFail`

- This error may occur if you are using `libtorch.so` from the Python package, which does not include all necessary dependencies.

## VSCode Environment Variables Not Updated for Rust Analyzer Actions

- **Solution:** Restart VSCode to refresh environment variables.

## `LD_LIBRARY_PATH` Missing Paths Outside Target

- Refer to the [Rust Cargo Documentation](https://doc.rust-lang.org/cargo/reference/environment-variables.html#dynamic-library-paths) for dynamic library paths.

## Unresolved Import Errors

- This might be due to a mismatched edition key in `Cargo.toml`.

## VSCode Extension Not Working Without Error Messages

- Ensure there are no type errors in TypeScript code.
- Compare with `rust-analyzer` as a last resort.
- Watch for infinite loops.

## Couldn’t Find VSCode Publisher

- Refer to [VSCode Marketplace](https://marketplace.visualstudio.com/manage/publishers/husky-lang).

## `lsp-type` Version Issues

- **Note:** Version 94.1 is problematic due to numerous bugs; use 94.0 instead.

## `debug_with_db` Not Working

- Ensure that the `db` trait extends the other `db` trait.

## Introducing a Dependency Breaks Things

- The issue might be due to feature flags introduced by the dependency, affecting other dependencies (e.g., `smallvec/union`).

## Consolidating Dependency Versions

- Use the command:

  ```bash
  cargo update -p bson:0.11.1 --precise 0.10.0
  ```

## Macro Trailing Commas

- Example of handling optional trailing commas in macros:

  ```rust
  ($Name:ident { $($Variant:ident),* $(,)? }) => {
  //                                 ^^^^^
  ```

- [Read more on Stack Overflow](https://stackoverflow.com/questions/43143327/how-to-allow-optional-trailing-commas-in-macros).

## LLDB Not Showing Full Path

- Set the frame format with the following command:

  ```lldb
  settings set frame-format frame #${frame.index}: ${frame.pc}{ ${module.file.basename}{\`${function.name}}}{ at ${line.file.fullpath}:${line.number}}\n
  ```

## Lean Server Outputting `fwIn.txt`, `fwOut.txt`, `wdErr.txt`, `wdIn.txt`, `wdOut.txt`

- Search for "Server Logging: Enabled" in its settings.

## `#[cfg(test)]` Not Running During Testing in `linkages_emancipated_by_javelin`

- This issue is still under investigation.

## VSCode Regex

- It’s highly recommended to read [Using Regular Expressions in Visual Studio](https://learn.microsoft.com/en-us/visualstudio/ide/using-regular-expressions-in-visual-studio?view=vs-2022).
- Captured groups are particularly useful.

## The `path` Attribute

- Refer to the [Rust Documentation](https://doc.rust-lang.org/reference/items/modules.html) for details on the `path` attribute.

## `ld.lld: error: unable to find library -lstdc++`

- Try installing the appropriate version of `libstdc++`:

```bash
sudo apt install libstdc++-14-dev
```

or another relevant version.

## Tracing

- **Crate Name:** Ensure the crate name is in snake case.

```rust
tracing_subscriber::registry()
    .with(tracing_subscriber::EnvFilter::new(
        "husky_websocket_utils=info",
    ))
    .with(tracing_subscriber::fmt::layer())
    .init();
```

## Rust Panic

panic using any type:

```rust
std::panic::panic_any(t)
```

## Rust Macro

### How to use variadic macros to call nested constructors?

<https://stackoverflow.com/questions/24512356/how-to-use-variadic-macros-to-call-nested-constructors>

### catch unwind anything

<https://doc.rust-lang.org/std/panic/struct.AssertUnwindSafe.html>

## rust item path not found by pub use

Maybe it got shadowed in the way.

## vm

### vm value not recorded

crates/vmir/husky-vmir/src/expr.rs not using eval_expr_itself properly

## raw string tabs

vscode will convert tab into space even for raw string, be careful