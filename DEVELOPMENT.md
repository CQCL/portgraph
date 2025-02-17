# Welcome to the portgraph development guide <!-- omit in toc -->

This guide is intended to help you get started with developing portgraph.

If you find any errors or omissions in this document, please [open an issue](https://github.com/CQCL/portgraph/issues/new)!

## #️⃣ Setting up the development environment

You can setup the development environment you will need:

- Rust: https://www.rust-lang.org/tools/install

You can use the git hook in [`.github/pre-commit`](.github/pre-commit) to automatically run the test and check formatting before committing.
To install it, run:

```bash
ln -s .github/pre-commit .git/hooks/pre-commit
# Or, to check before pushing instead
ln -s .github/pre-commit .git/hooks/pre-push
```

## 🏃 Running the tests

To compile and test the rust code, run:

```bash
cargo build
cargo test
```

Finally, if you have rust nightly installed, you can run `miri` to detect
undefined behaviour in the code.

```bash
cargo +nightly miri test
```

## 🏋️ Benchmarking

We use two kinds of benchmarks in this project:

- A wall-clock time benchmark using `criterion`. This measures the time taken to
  run a function by running it multiple times.
- A single-shot instruction count / memory hits benchmark using `iai-callgrind`.
  This measures the number of instructions executed and the number of cache hits
  and misses.

Both tools run the same set of test cases.

When profiling and debugging performance issues, you may also want to use
[samply](https://github.com/mstange/samply) to visualize the see flame graphs of
specific examples.

### Wall-clock time benchmarks

This is the simplest kind of benchmark. To run the, use:

```bash
cargo bench --bench criterion_benches
```

We run these on CI to track historical performance using a special single-shot test harness,
and upload them to [codspeed.io](https://codspeed.io/CQCL/portgraph).

### Single-shot benchmarking

These benchmarks are useful when running in noisy environments, in addition to
being faster than criterion.

To run these, you must have [`valgrind`](https://valgrind.org/) installed.
Support for Apple Silicon (M1/M2/...) macs is
[experimental](https://github.com/LouisBrunner/valgrind-macos/issues/56), so you
will need to manually clone and compile the branch. See
[`LouisBrunner/valgrind-macos`](https://github.com/LouisBrunner/valgrind-macos/blob/feature/m1/README)
for instructions.

In addition to `valgrind`, you will need to install `iai-callgrind` runner. The
pre-build binaries are available on
[`cargo binstall`](https://github.com/cargo-bins/cargo-binstall).

```bash
cargo binstall iai-callgrind-runner
```

The benchmarks can then be run with:

```bash
cargo bench --bench iai_benches
```

## 💅 Coding Style

The rustfmt tool is used to enforce a consistent rust coding style. The CI will fail if the code is not formatted correctly.

To format your code, run:

```bash
# Format rust code
cargo fmt
```

We also check for clippy warnings, which are a set of linting rules for rust. To run clippy, run:

```bash
cargo clippy --all-targets
```

## 📈 Code Coverage

We run coverage checks on the CI. Once you submit a PR, you can review the
line-by-line coverage report on
[codecov](https://app.codecov.io/gh/CQCL/portgraph/commits?branch=All%20branches).

To run the coverage checks locally, install `cargo-llvm-cov`, generate the report with:
```bash
cargo llvm-cov --lcov > lcov.info
```

and open it with your favourite coverage viewer. In VSCode, you can use
[`coverage-gutters`](https://marketplace.visualstudio.com/items?itemName=ryanluker.vscode-coverage-gutters).

## 🌐 Contributing to portgraph

We welcome contributions to portgraph! Please open [an issue](https://github.com/CQCL/portgraph/issues/new) or [pull request](https://github.com/CQCL/portgraph/compare) if you have any questions or suggestions.

PRs should be made against the `main` branch, and should pass all CI checks before being merged. This includes using the [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/) format for the PR title.

The general format of a contribution title should be:

```
<type>(<scope>)!: <description>
```

Where the scope is optional, and the `!` is only included if this is a semver breaking change that requires a major version bump.

We accept the following contribution types:

- feat: New features.
- fix: Bug fixes.
- docs: Improvements to the documentation.
- style: Formatting, missing semi colons, etc; no code change.
- refactor: Refactoring code without changing behaviour.
- perf: Code refactoring focused on improving performance.
- test: Adding missing tests, refactoring tests; no production code change.
- ci: CI related changes. These changes are not published in the changelog.
- chore: Updating build tasks, package manager configs, etc. These changes are not published in the changelog.
- revert: Reverting previous commits.