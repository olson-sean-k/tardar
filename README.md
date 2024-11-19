**Tardar** is a Rust library that provides extensions for the [`miette`] crate.
These extensions primarily provide diagnostic `Result`s and ergonomic
aggregation and collation of `Diagnostic`s.

[![GitHub](https://img.shields.io/badge/GitHub-olson--sean--k/tardar-8da0cb?logo=github&style=for-the-badge)](https://github.com/olson-sean-k/tardar)
[![docs.rs](https://img.shields.io/badge/docs.rs-tardar-66c2a5?logo=rust&style=for-the-badge)](https://docs.rs/tardar)
[![crates.io](https://img.shields.io/crates/v/tardar.svg?logo=rust&style=for-the-badge)](https://crates.io/crates/tardar)

## Diagnostic Results

`DiagnosticResult` is a `Result` type that aggregates `Diagnostic`s associated
with an output type `T` in both the success and failure case (`Ok` and `Err`
variants). The `Ok` variant contains a `Diagnosed<T>` with zero or more
non-error `Diagnostic`s. The `Err` variant contains an `Error<'_>` with one or
more `Diagnostic`s where at least one `Diagnostic` is considered an error.

Together with extension methods, `DiagnosticResult` supports fluent and
ergonomic use of diagnostic functions (functions that return a
`DiagnosticResult`). For example, a library that parses a data structure or
language can aggregate `Diagnostic`s when combining functions.

```rust
pub fn parse_and_check(
    expression: &str,
) -> DiagnosticResult<'_, Checked<Ast<'_>>> {
    ast::parse(expression)
        .and_then_diagnose(rule::check)
        .and_then_diagnose(|tree| hint::check(&tree).map_output(|_| tree))
}
```

Here, `and_then_diagnose` is much like the standard `Result::and_then`, but
accepts a diagnostic function and preserves any input `Diagnostic`s. Similarly,
`map_output` resembles `Result::map`, but instead maps only the output `T` and
forwards `Diagnostic`s.

`DiagnosticResult`s can be constructed from related types, such as `Result`
types of a single error `Diagnostic` or iterators with `Diagnostic` items.

```rust
fn parse(expression: &str) -> Result<Ast<'_>, ParseError> { ... }

fn analyze(tree: &Ast) -> impl '_ + Iterator<Item = BoxedDiagnostic<'_>> { ... }

pub fn parse_and_analyze(expression: &str) -> DiagnosticResult<'_, Ast<'_>> {
    parse(expression)
        .into_error_diagnostic()
        .and_then_diagnose(|tree| analyze(&tree).into_non_error_diagnostic());
}
```

## Collation

[`miette`]: https://crates.io/crates/miette
