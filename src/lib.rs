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
use mitsein::iter1::{Extend1, FromIterator1, IntoIterator1, Iterator1, IteratorExt as _};
use mitsein::slice1::Slice1;
use mitsein::vec1::Vec1;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::{Chain, Flatten};
use std::option;

pub mod integration {
    pub mod miette {
        #[doc(hidden)]
        pub use ::miette::*;
    }
}

pub mod prelude {
    pub use crate::{DiagnosticResultExt as _, ErrorExt as _, IteratorExt as _, ResultExt as _};
}

type Related<'d> = Flatten<option::IntoIter<Box<dyn Iterator<Item = &'d dyn Diagnostic> + 'd>>>;
type HeadAndRelated<'d> = Chain<option::IntoIter<&'d dyn Diagnostic>, Related<'d>>;

pub trait DiagnosticExt: Diagnostic {
    fn tree(&self) -> Iterator1<Tree<'_>>;
}

impl<D> DiagnosticExt for D
where
    D: Diagnostic,
{
    fn tree(&self) -> Iterator1<Tree<'_>> {
        // SAFETY: This `Tree` iterator must yield one or more items. `self` is pushed onto the
        //         stack and is popped and yielded in the `Iterator` implementation for `Tree`, so
        //         this `Tree` iterator always yields `self`.
        unsafe {
            Iterator1::from_iter_unchecked(Tree {
                stack: vec![Some(self as &dyn Diagnostic)
                    .into_iter()
                    .chain(None.into_iter().flatten())],
                related: None.into_iter().chain(None.into_iter().flatten()),
            })
        }
    }
}

pub struct Tree<'d> {
    stack: Vec<HeadAndRelated<'d>>,
    related: HeadAndRelated<'d>,
}

impl<'d> Debug for Tree<'d> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Tree")
            .field("stack", &"..")
            .field("related", &"..")
            .finish()
    }
}

impl<'d> Iterator for Tree<'d> {
    type Item = &'d dyn Diagnostic;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(diagnostic) = self.related.next() {
                self.stack.push(
                    None.into_iter()
                        .chain(diagnostic.related().into_iter().flatten()),
                );
                return Some(diagnostic);
            }
            else if let Some(related) = self.stack.pop() {
                self.related = related;
            }
            else {
                return None;
            }
        }
    }
}

pub trait ErrorExt: error::Error {
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
        Collation::from(self)
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

pub trait AsDiagnosticObject {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic;
}

impl<'d, T> AsDiagnosticObject for &'d T
where
    T: AsDiagnosticObject + ?Sized,
{
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        T::as_diagnostic_object(*self)
    }
}

impl<'d> AsDiagnosticObject for BoxedDiagnostic<'d> {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self.as_ref()
    }
}

impl AsDiagnosticObject for dyn Diagnostic {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self
    }
}

pub trait AsDiagnosticSlice1 {
    type Diagnostic: AsDiagnosticObject;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic>;
}

impl<'c, T> AsDiagnosticSlice1 for &'c T
where
    T: AsDiagnosticSlice1 + ?Sized,
{
    type Diagnostic = T::Diagnostic;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        T::as_diagnostic_slice1(*self)
    }
}

impl<D> AsDiagnosticSlice1 for Slice1<D>
where
    D: AsDiagnosticObject,
{
    type Diagnostic = D;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        self
    }
}

impl<D> AsDiagnosticSlice1 for Vec1<D>
where
    D: AsDiagnosticObject,
{
    type Diagnostic = D;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        self
    }
}

#[repr(transparent)]
pub struct Collation<T>(T);

impl<T> Collation<T>
where
    T: AsDiagnosticSlice1,
{
    fn first(&self) -> &dyn Diagnostic {
        self.0.as_diagnostic_slice1().first().as_diagnostic_object()
    }

    pub fn codes(&self) -> impl '_ + Iterator<Item = Box<dyn Display + '_>> {
        self.0
            .as_diagnostic_slice1()
            .iter()
            .flat_map(|diagnostic| diagnostic.as_diagnostic_object().code())
    }

    pub fn severities(&self) -> impl '_ + Iterator<Item = Severity> {
        self.0
            .as_diagnostic_slice1()
            .iter()
            .flat_map(|diagnostic| diagnostic.as_diagnostic_object().severity())
    }
}

impl<T> Debug for Collation<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.debug_tuple("Collation").field(&"..").finish()
    }
}

impl<T> Diagnostic for Collation<T>
where
    T: AsDiagnosticSlice1,
{
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.first().code()
    }

    fn severity(&self) -> Option<Severity> {
        self.first().severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.first().help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        self.first().url()
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.first().source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        self.first().labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self.0
            .as_diagnostic_slice1()
            .iter()
            .skip(1)
            .try_into_iter1()
            .ok()
            .map(|diagnostics| {
                Box::new(
                    diagnostics
                        .into_iter()
                        .map(AsDiagnosticObject::as_diagnostic_object),
                ) as Box<dyn Iterator<Item = &dyn Diagnostic>>
            })
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.first().diagnostic_source()
    }
}

impl<T> Display for Collation<T>
where
    T: AsDiagnosticSlice1,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self
            .0
            .as_diagnostic_slice1()
            .iter()
            .map(AsDiagnosticObject::as_diagnostic_object)
        {
            writeln!(formatter, "{}", diagnostic)?;
        }
        Ok(())
    }
}

impl<T> error::Error for Collation<T>
where
    T: AsDiagnosticSlice1,
{
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        self.first().source()
    }
}

impl<'d> From<Error<'d>> for Collation<Vec1<BoxedDiagnostic<'d>>> {
    fn from(error: Error<'d>) -> Self {
        Collation::from(error.into_diagnostics())
    }
}

impl<'c, D> From<&'c Slice1<D>> for Collation<&'c Slice1<D>>
where
    D: AsDiagnosticObject,
{
    fn from(diagnostics: &'c Slice1<D>) -> Self {
        Collation(diagnostics)
    }
}

impl<D> From<Vec1<D>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject,
{
    fn from(diagnostics: Vec1<D>) -> Self {
        Collation(diagnostics)
    }
}

impl<D> FromIterator1<D> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject,
{
    fn from_iter1<I>(items: I) -> Self
    where
        I: IntoIterator1<Item = D>,
    {
        Collation::from(Vec1::from_iter1(items))
    }
}

impl<'c, D> TryFrom<&'c [D]> for Collation<&'c Slice1<D>>
where
    D: AsDiagnosticObject,
{
    type Error = &'c [D];

    fn try_from(diagnostics: &'c [D]) -> Result<Self, Self::Error> {
        Slice1::try_from_slice(diagnostics).map(Collation::from)
    }
}

impl<'d, T> TryFrom<Diagnosed<'d, T>> for Collation<Vec1<BoxedDiagnostic<'d>>> {
    type Error = Diagnosed<'d, T>;

    fn try_from(diagnosed: Diagnosed<'d, T>) -> Result<Self, Self::Error> {
        let Diagnosed(output, diagnostics) = diagnosed;
        Vec1::try_from(diagnostics)
            .map(Collation::from)
            .map_err(|diagnostics| Diagnosed(output, diagnostics))
    }
}

impl<D> TryFrom<Vec<D>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject,
{
    type Error = Vec<D>;

    fn try_from(diagnostics: Vec<D>) -> Result<Self, Self::Error> {
        Vec1::try_from(diagnostics).map(Collation::from)
    }
}
