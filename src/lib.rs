//! **Tardar** is a library that provides extensions for the [`miette`] crate. [Diagnostic
//! `Result`][`DiagnosticResult`]s are the primary extension, which pair an output with aggregated
//! [`Diagnostic`]s in both the `Ok` and `Err` variants.
//!
//! [`Diagnostic`]: miette::Diagnostic
//! [`DiagnosticResult`]: crate::DiagnosticResult
//! [`Result`]: std::result::Result
//!
//! [`miette`]: https://crates.io/crates/miette

use miette::{Diagnostic, LabeledSpan, Severity, SourceCode};
use mitsein::iter1::{Extend1, IntoIterator1, Iterator1, IteratorExt as _};
use mitsein::slice1::Slice1;
use mitsein::vec1::Vec1;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Deref;

pub mod integration {
    pub mod miette {
        #[doc(hidden)]
        pub use ::miette::*;
    }
}

pub mod prelude {
    pub use crate::{DiagnosticResultExt as _, IteratorExt as _, ResultExt as _};
}

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
        Ok(Diagnosed((), self.collect()))
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
            Ok(output) => Ok(Diagnosed(output, vec![])),
            Err(error) => Err(Error([Box::from_diagnostic(error)].into())),
        }
    }
}

pub type BoxedDiagnostic<'d> = Box<dyn Diagnostic + 'd>;

pub trait BoxedDiagnosticExt<'d> {
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
/// On success, the `Ok` variant contains zero or more diagnostics and a non-diagnostic output `T`.
/// On failure, the `Err` variant contains one or more diagnostics, where at least one of the
/// diagnostics is an error.
///
/// See [`DiagnosticResultExt`].
///
/// [`Diagnostic`]: miette::Diagnostic
/// [`DiagnosticResultExt`]: crate::DiagnosticResultExt
pub type DiagnosticResult<'d, T> = Result<Diagnosed<'d, T>, Error<'d>>;

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
            Ok(Diagnosed(output, mut diagnostics)) => match f(output) {
                Ok(Diagnosed(output, tail)) => {
                    diagnostics.extend(tail);
                    Ok(Diagnosed(output, diagnostics))
                }
                Err(tail) => Err(Error(diagnostics.extend_non_empty(tail))),
            },
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

#[derive(Debug)]
pub struct Diagnosed<'d, T>(pub T, pub Vec<BoxedDiagnostic<'d>>);

impl<'d, T> Diagnosed<'d, T> {
    pub fn into_output(self) -> T {
        self.0
    }

    pub fn into_diagnostics(self) -> Vec<BoxedDiagnostic<'d>> {
        self.1
    }

    pub fn map_output<U, F>(self, f: F) -> Diagnosed<'d, U>
    where
        F: FnOnce(T) -> U,
    {
        let Diagnosed(output, diagnostics) = self;
        Diagnosed(f(output), diagnostics)
    }

    pub fn collate(self) -> (T, Option<Collation<Vec1<BoxedDiagnostic<'d>>>>) {
        let Diagnosed(output, diagnostics) = self;
        (
            output,
            Vec1::try_from(diagnostics).ok().map(Collation::from),
        )
    }

    pub fn output(&self) -> &T {
        &self.0
    }

    pub fn diagnostics(&self) -> &[BoxedDiagnostic<'d>] {
        self.1.as_slice()
    }

    pub fn has_diagnostics(&self) -> bool {
        !self.1.is_empty()
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Error<'d>(pub Vec1<BoxedDiagnostic<'d>>);

impl<'d> Error<'d> {
    pub fn into_diagnostics(self) -> Vec1<BoxedDiagnostic<'d>> {
        self.0
    }

    pub fn collate(self) -> Collation<Vec1<BoxedDiagnostic<'d>>> {
        self.0.into()
    }

    pub fn diagnostics(&self) -> &Slice1<BoxedDiagnostic<'d>> {
        self.0.as_slice1()
    }
}

impl<'d> Display for Error<'d> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self.diagnostics().iter1() {
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

#[derive(Debug)]
#[repr(transparent)]
pub struct Collation<D>(D);

impl<'b, 'd> Diagnostic for Collation<&'b Slice1<BoxedDiagnostic<'d>>> {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().code()
    }

    fn severity(&self) -> Option<Severity> {
        self.0.first().severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().url()
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.0.first().source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        self.0.first().labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self::tail(self.0.iter())
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.0.first().diagnostic_source()
    }
}

impl<'d> Diagnostic for Collation<Vec1<BoxedDiagnostic<'d>>> {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().code()
    }

    fn severity(&self) -> Option<Severity> {
        self.0.first().severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.0.first().url()
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.0.first().source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        self.0.first().labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self::tail(self.0.iter())
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.0.first().diagnostic_source()
    }
}

impl<'d, D> Display for Collation<D>
where
    D: Deref<Target = Slice1<BoxedDiagnostic<'d>>>,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self.0.iter1() {
            writeln!(formatter, "{}", diagnostic)?;
        }
        Ok(())
    }
}

impl<'d, D> error::Error for Collation<D> where
    D: Deref<Target = Slice1<BoxedDiagnostic<'d>>> + Debug
{
}

impl<'b, 'd> From<&'b Slice1<BoxedDiagnostic<'d>>> for Collation<&'b Slice1<BoxedDiagnostic<'d>>> {
    fn from(diagnostics: &'b Slice1<BoxedDiagnostic<'d>>) -> Self {
        Collation(diagnostics)
    }
}

impl<'d> From<Vec1<BoxedDiagnostic<'d>>> for Collation<Vec1<BoxedDiagnostic<'d>>> {
    fn from(diagnostics: Vec1<BoxedDiagnostic<'d>>) -> Self {
        Collation(diagnostics)
    }
}

impl<'b, 'd> TryFrom<&'b [BoxedDiagnostic<'d>]> for Collation<&'b Slice1<BoxedDiagnostic<'d>>> {
    type Error = &'b [BoxedDiagnostic<'d>];

    fn try_from(diagnostics: &'b [BoxedDiagnostic<'d>]) -> Result<Self, Self::Error> {
        Slice1::try_from_slice(diagnostics).map(Collation)
    }
}

impl<'d> TryFrom<Vec<BoxedDiagnostic<'d>>> for Collation<Vec1<BoxedDiagnostic<'d>>> {
    type Error = Vec<BoxedDiagnostic<'d>>;

    fn try_from(diagnostics: Vec<BoxedDiagnostic<'d>>) -> Result<Self, Self::Error> {
        Vec1::try_from(diagnostics).map(Collation)
    }
}

fn tail<'a, I>(diagnostics: I) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>>
where
    I: IntoIterator<Item = &'a Box<dyn Diagnostic + 'a>>,
    I::IntoIter: 'a,
{
    diagnostics
        .into_iter()
        .skip(1)
        .try_into_iter1()
        .ok()
        .map(|diagnostics| {
            Box::new(diagnostics.into_iter().map(AsRef::as_ref))
                as Box<dyn Iterator<Item = &dyn Diagnostic>>
        })
}
