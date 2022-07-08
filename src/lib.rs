//! **Tardar** is a library that provides extensions for the [`miette`] crate. [Diagnostic
//! `Result`][`DiagnosticResult`]s are the primary extension, which pair an output with aggregated
//! [`Diagnostic`]s in both the `Ok` and `Err` variants.
//!
//! [`Diagnostic`]: miette::Diagnostic
//! [`DiagnosticResult`]: crate::DiagnosticResult
//! [`Result`]: std::result::Result
//!
//! [`miette`]: https://crates.io/crates/miette

use miette::Diagnostic;
use vec1::{vec1, Vec1};

pub mod integration {
    pub mod miette {
        #[doc(hidden)]
        pub use ::miette::*;
    }
}

pub mod prelude {
    pub use crate::{DiagnosticResultExt as _, IteratorExt as _, ResultExt as _};
}

pub type BoxedDiagnostic<'d> = Box<dyn Diagnostic + 'd>;

/// `Result` that includes [`Diagnostic`]s on both success and failure.
///
/// On success, the `Ok` variant contains zero or more diagnostics and a non-diagnostic output `T`.
/// On failure, the `Err` variant contains one or more diagnostics, where at least one of the
/// diagnostics is an error.
///
/// See [`DiagnosticResultExt`].
///
/// [`Diagnostic`]: miette::Diagnostic
/// [`DiagnosticResultExt`]: crate::DiagnosticResultExt
pub type DiagnosticResult<'d, T> = Result<(T, Vec<BoxedDiagnostic<'d>>), Vec1<BoxedDiagnostic<'d>>>;

/// Extension methods for [`Iterator`]s.
///
/// [`Iterator`]: std::iter::Iterator
pub trait IteratorExt: Iterator + Sized {
    /// Converts from a type that implements `Iterator<Item = BoxedDiagnostic<'d>>` into
    /// `DiagnosticResult<'d, ()>`.
    ///
    /// The [`Diagnostic`] items of the iterator are interpreted as non-errors. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`]s may have error-level severities
    /// despite being interpreted as non-errors.
    ///
    /// [`Diagnostic`]: miette::Diagnostic
    /// [`Severity`]: miette::Severity
    fn into_non_error_diagnostic<'d>(self) -> DiagnosticResult<'d, ()>
    where
        Self: Iterator<Item = BoxedDiagnostic<'d>>;
}

impl<I> IteratorExt for I
where
    I: Iterator,
{
    fn into_non_error_diagnostic<'d>(self) -> DiagnosticResult<'d, ()>
    where
        Self: Iterator<Item = BoxedDiagnostic<'d>>,
    {
        Ok(((), self.collect()))
    }
}

/// Extension methods for [`Result`]s.
///
/// [`Result`]: std::result::Result
pub trait ResultExt<T, E> {
    /// Converts from `Result<T, E>` into `DiagnosticResult<'d, T>`.
    ///
    /// The error type `E` must be a [`Diagnostic`] and is interpreted as an error. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`] may have a non-error severity
    /// despite being interpreted as an error.
    ///
    /// [`Diagnostic`]: miette::Diagnostic
    /// [`Severity`]: miette::Severity
    fn into_error_diagnostic<'d>(self) -> DiagnosticResult<'d, T>
    where
        E: 'd + Diagnostic;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_error_diagnostic<'d>(self) -> DiagnosticResult<'d, T>
    where
        E: 'd + Diagnostic,
    {
        match self {
            Ok(output) => Ok((output, vec![])),
            Err(error) => Err(vec1![Box::new(error) as Box<dyn Diagnostic + 'd>]),
        }
    }
}

/// Extension methods for [`DiagnosticResult`]s.
///
/// [`DiagnosticResult`]: crate::DiagnosticResult
pub trait DiagnosticResultExt<'d, T> {
    /// Converts from `DiagnosticResult<'_, T>` into `Option<T>`.
    ///
    /// This function is similar to [`Result::ok`], but gets only the non-diagnostic output `T`
    /// from the `Ok` variant in [`DiagnosticResult`], discarding diagnostics.
    ///
    /// [`DiagnosticResult`]: crate::DiagnosticResult
    /// [`Result::ok`]: std::result::Result::ok
    fn ok_output(self) -> Option<T>;

    /// Gets the [`Diagnostic`]s associated with the [`DiagnosticResult`].
    ///
    /// Both the success and failure case may include diagnostics.
    ///
    /// [`Diagnostic`]: miette::Diagnostic
    /// [`DiagnosticResult`]: crate::DiagnosticResult
    fn diagnostics(&self) -> &[BoxedDiagnostic<'d>];

    /// Maps `DiagnosticResult<'d, T>` into `DiagnosticResult<'d, U>` by applying a function over
    /// the non-diagnostic output of the `Ok` variant.
    ///
    /// This function is similar to [`Result::map`], but maps only the non-diagnostic output `T`
    /// from the `Ok` variant in [`DiagnosticResult`], ignoring diagnostics.
    ///
    /// [`DiagnosticResult`]: crate::DiagnosticResult
    /// [`Result::map`]: std::result::Result::map
    fn map_output<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> U;

    /// Calls the given function if the `DiagnosticResult` is `Ok` and otherwise returns the `Err`
    /// variant of the `DiagnosticResult`.
    ///
    /// This function is similar to [`Result::and_then`], but additionally forwards and collects
    /// diagnostics.
    ///
    /// [`DiagnosticResult`]: crate::DiagnosticResult
    /// [`Result::and_then`]: std::result::Result::and_then
    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'d, U>;
}

impl<'d, T> DiagnosticResultExt<'d, T> for DiagnosticResult<'d, T> {
    fn ok_output(self) -> Option<T> {
        match self {
            Ok((output, _)) => Some(output),
            _ => None,
        }
    }

    fn diagnostics(&self) -> &[BoxedDiagnostic<'d>] {
        match self {
            Ok((_, ref diagnostics)) => diagnostics,
            Err(ref diagnostics) => diagnostics,
        }
    }

    fn map_output<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok((output, diagnostics)) => Ok((f(output), diagnostics)),
            Err(diagnostics) => Err(diagnostics),
        }
    }

    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'d, U>,
    {
        match self {
            Ok((output, mut diagnostics)) => match f(output) {
                Ok((output, tail)) => {
                    diagnostics.extend(tail);
                    Ok((output, diagnostics))
                }
                Err(tail) => {
                    diagnostics.extend(tail);
                    Err(diagnostics
                        .try_into()
                        .expect("diagnostic failure with no errors"))
                }
            },
            Err(diagnostics) => Err(diagnostics),
        }
    }
}
