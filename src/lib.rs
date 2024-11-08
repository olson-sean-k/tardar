//! **Tardar** is a library that provides extensions for the [`miette`] crate. [Diagnostic
//! `Result`][`DiagnosticResult`]s are the primary extension, which aggregate [`Diagnostic`]s in
//! both the `Ok` and `Err` variants.

use miette::Diagnostic;
use mitsein::iter1::{Extend1, IntoIterator1, Iterator1};
use mitsein::slice1::Slice1;
use mitsein::vec1::Vec1;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};

pub mod integration {
    pub mod miette {
        #[doc(hidden)]
        pub use ::miette::*;
    }
}

pub mod prelude {
    pub use crate::{
        BoxedDiagnosticExt as _, DiagnosticResultExt as _, ErrorExt as _, IteratorExt as _,
        ResultExt as _,
    };
}

/// Extension methods for [`Error`][`error::Error`]s.
pub trait ErrorExt: error::Error {
    /// Gets an iterator over the sources of the `Error`.
    ///
    /// The returned iterator successively calls [`Error::source`][`error::Error::source`] to yield
    /// a chain of error sources.
    fn sources(&self) -> Sources<'_>;
}

impl<E> ErrorExt for E
where
    E: error::Error,
{
    fn sources(&self) -> Sources<'_> {
        Sources {
            source: self.source(),
        }
    }
}

/// An [`Iterator`] over sources of an [`Error`][`error::Error`].
#[derive(Debug)]
pub struct Sources<'e> {
    source: Option<&'e dyn error::Error>,
}

impl<'e> Iterator for Sources<'e> {
    type Item = &'e dyn error::Error;

    fn next(&mut self) -> Option<Self::Item> {
        self.source.take().map(|next| {
            self.source = next.source();
            next
        })
    }
}

/// Extension methods for [`Iterator`]s.
pub trait IteratorExt: Iterator + Sized {
    /// Converts from a type that implements `Iterator<Item = BoxedDiagnostic<'d>>` into
    /// `DiagnosticResult<'d, ()>`.
    ///
    /// The [`Diagnostic`] items of the iterator are interpreted as non-errors. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`]s may have error-level severities
    /// despite being interpreted as non-errors.
    ///
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
        Ok(Diagnosed((), self.collect()))
    }
}

/// Extension methods for [`Result`]s.
pub trait ResultExt<T, E> {
    /// Converts from `Result<T, E>` into `DiagnosticResult<'d, T>`.
    ///
    /// The error type `E` must be a [`Diagnostic`] and is interpreted as an error. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`] may have a non-error severity
    /// despite being interpreted as an error.
    ///
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
            Ok(output) => Ok(Diagnosed(output, vec![])),
            Err(error) => Err(Error([Box::from_diagnostic(error)].into())),
        }
    }
}

pub type BoxedDiagnostic<'d> = Box<dyn Diagnostic + 'd>;

/// Extension methods for [`BoxedDiagnostic`]s.
pub trait BoxedDiagnosticExt<'d> {
    /// Constructs a [`BoxedDiagnostic`] from a [`Diagnostic`].
    fn from_diagnostic<D>(diagnostic: D) -> Self
    where
        D: Diagnostic + 'd;
}

impl<'d> BoxedDiagnosticExt<'d> for BoxedDiagnostic<'d> {
    fn from_diagnostic<D>(diagnostic: D) -> Self
    where
        D: Diagnostic + 'd,
    {
        Box::new(diagnostic) as Box<dyn Diagnostic + 'd>
    }
}

/// `Result` that includes [`Diagnostic`]s on both success and failure.
///
/// On success, the `Ok` variant contains a [`Diagnosed`] with zero or more diagnostics and an
/// output `T`. On failure, the `Err` variant contains an [`Error`] with one or more diagnostics,
/// where at least one of the diagnostics has been interpreted as an error.
pub type DiagnosticResult<'d, T> = Result<Diagnosed<'d, T>, Error<'d>>;

/// Extension methods for [`DiagnosticResult`]s.
pub trait DiagnosticResultExt<'d, T> {
    /// Converts from `DiagnosticResult<'_, T>` into `Option<T>`.
    ///
    /// This function is similar to [`Result::ok`], but gets only the output `T` from the
    /// [`Diagnosed`] in the `Ok` variant, discarding any diagnostics.
    fn ok_output(self) -> Option<T>;

    /// Gets the [`Diagnostic`]s associated with the [`DiagnosticResult`].
    fn diagnostics(&self) -> &[BoxedDiagnostic<'d>];

    /// Maps `DiagnosticResult<'d, T>` into `DiagnosticResult<'d, U>` by applying a function over
    /// the output `T` of the `Ok` variant.
    ///
    /// This function is similar to [`Result::map`], but maps only the non-diagnostic output `T`
    /// from the `Ok` variant in [`DiagnosticResult`], ignoring diagnostics.
    fn map_output<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> U;

    /// Calls the given diagnostic function if the `DiagnosticResult` is `Ok` and otherwise returns
    /// the `Err` variant of the `DiagnosticResult`.
    ///
    /// This function is similar to [`Result::and_then`], but additionally forwards and collects
    /// diagnostics.
    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'d, U>;

    /// Returns `true` if the `DiagnosticResult` has one or more associated [`Diagnostic`]s.
    fn has_diagnostics(&self) -> bool;
}

impl<'d, T> DiagnosticResultExt<'d, T> for DiagnosticResult<'d, T> {
    fn ok_output(self) -> Option<T> {
        match self {
            Ok(Diagnosed(output, _)) => Some(output),
            _ => None,
        }
    }

    fn diagnostics(&self) -> &[BoxedDiagnostic<'d>] {
        match self {
            Ok(ref diagnosed) => diagnosed.diagnostics(),
            Err(ref error) => error.diagnostics(),
        }
    }

    fn map_output<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(diagnosed) => Ok(diagnosed.map_output(f)),
            Err(error) => Err(error),
        }
    }

    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'d, U>,
    {
        match self {
            Ok(diagnosed) => diagnosed.and_then_diagnose(f),
            Err(diagnostics) => Err(diagnostics),
        }
    }

    fn has_diagnostics(&self) -> bool {
        match self {
            Ok(ref diagnosed) => diagnosed.has_diagnostics(),
            Err(_) => true,
        }
    }
}

/// A diagnosed `T`.
///
/// `Diagnosed` pairs an output `T` with zero or more non-error [`Diagnostic`]s. In the strictest
/// sense, here non-error merely means that no associated [`Diagnostic`]s prevented the
/// construction of the output `T`. The [`Severity`] of the associated [`Diagnostic`]s is
/// arbitrary.
///
/// See [`DiagnosticResult`].
///
/// [`Severity`]: miette::Severity
#[derive(Debug)]
pub struct Diagnosed<'d, T>(pub T, pub Vec<BoxedDiagnostic<'d>>);

impl<'d, T> Diagnosed<'d, T> {
    /// Converts from `Diagnosed` into its output `T`, discarding any [`Diagnostic`]s.
    pub fn into_output(self) -> T {
        self.0
    }

    /// Converts from `Diagnosed` into its associated [`Diagnostic`]s, discarding the output `T`.
    pub fn into_diagnostics(self) -> Vec<BoxedDiagnostic<'d>> {
        self.1
    }

    /// Maps `Diagnosed<'d, T>` into `Diagnosed<'d, U>` by applying a function over the output `T`.
    pub fn map_output<U, F>(self, f: F) -> Diagnosed<'d, U>
    where
        F: FnOnce(T) -> U,
    {
        let Diagnosed(output, diagnostics) = self;
        Diagnosed(f(output), diagnostics)
    }

    /// Calls the given diagnostic function with the output `T` and aggregates [`Diagnostic`]s into
    /// a [`DiagnosticResult`].
    pub fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'d, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'d, U>,
    {
        let Diagnosed(output, mut diagnostics) = self;
        match f(output) {
            Ok(Diagnosed(output, tail)) => {
                diagnostics.extend(tail);
                Ok(Diagnosed(output, diagnostics))
            }
            Err(Error(tail)) => Err(Error(diagnostics.extend_non_empty(tail))),
        }
    }

    /// Gets the output `T`.
    pub fn output(&self) -> &T {
        &self.0
    }

    /// Gets the [`Diagnostic`]s associated with the output `T`.
    pub fn diagnostics(&self) -> &[BoxedDiagnostic<'d>] {
        self.1.as_slice()
    }

    /// Returns `true` if the `Diagnosed` has one or more associated [`Diagnostic`]s.
    pub fn has_diagnostics(&self) -> bool {
        !self.1.is_empty()
    }
}

/// A diagnostic error.
///
/// `Error` contains one or more [`Diagnostic`]s where at least one has been interpreted as an
/// error. Any [`Diagnostic`] can be interpreted as an error and the [`Severity`] of
/// [`Diagnostic`]s in an `Error` are arbitrary.
///
/// `Error` implements [the standard `Error` trait][`error::Error`] and displays its associated
/// [`Diagnostic`]s serially when formatted. `Error` is **not** itself a [`Diagnostic`].
///
/// See [`DiagnosticResult`].
///
/// [`Severity`]: miette::Severity
#[derive(Debug)]
#[repr(transparent)]
pub struct Error<'d>(pub Vec1<BoxedDiagnostic<'d>>);

impl<'d> Error<'d> {
    /// Converts from `Error` into its associated [`Diagnostic`]s.
    pub fn into_diagnostics(self) -> Vec1<BoxedDiagnostic<'d>> {
        self.0
    }

    /// Gets the associated [`Diagnostic`]s of the `Error`.
    pub fn diagnostics(&self) -> &Slice1<BoxedDiagnostic<'d>> {
        self.0.as_slice1()
    }
}

impl<'d> Display for Error<'d> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self.diagnostics().iter() {
            writeln!(formatter, "{}", diagnostic)?;
        }
        Ok(())
    }
}

impl<'d> error::Error for Error<'d> {}

impl<'d> IntoIterator for Error<'d> {
    type IntoIter = <Vec1<BoxedDiagnostic<'d>> as IntoIterator>::IntoIter;
    type Item = BoxedDiagnostic<'d>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'d> IntoIterator1 for Error<'d> {
    fn into_iter1(self) -> Iterator1<Self::IntoIter> {
        self.0.into_iter1()
    }
}
