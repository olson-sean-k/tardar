//! **Tardar** is a Rust library that provides extensions for the [`miette`] crate. These
//! extensions primarily provide diagnostic `Result`s and ergonomic aggregation and collation of
//! `Diagnostic`s.
//!
//! ## Diagnostic Results
//!
//! `DiagnosticResult` is a `Result` type that aggregates `Diagnostic`s associated with an output
//! type `T` in both the success and failure case (`Ok` and `Err` variants). The `Ok` variant
//! contains a `Diagnosed<T>` with zero or more non-error `Diagnostic`s. The `Err` variant contains
//! an `Error<'_>` with one or more `Diagnostic`s where at least one `Diagnostic` is considered an
//! error.
//!
//! Together with extension methods, `DiagnosticResult` supports fluent and ergonomic use of
//! diagnostic functions (functions that return a `DiagnosticResult`). For example, a library that
//! parses a data structure or language from text can aggregate `Diagnostic`s when combining
//! functions.
//!
//! ```rust
//! use tardar::prelude::*;
//! use tardar::{BoxedDiagnostic, DiagnosticResult};
//!
//! # struct Checked<T>(T);
//! # struct Ast<'t>(&'t str);
//! #
//! fn parse(expression: &str) -> DiagnosticResult<'_, Ast<'_>> {
//! #     tardar::Diagnosed::ok(Ast(expression)) /*
//!     ...
//! # */
//! }
//!
//! fn check<'t>(tree: Ast<'t>) -> DiagnosticResult<'t, Checked<Ast<'t>>> {
//! #     tardar::Diagnosed::ok(Checked(tree)) /*
//!     ...
//! # */
//! }
//!
//! pub fn parse_and_check(expression: &str) -> DiagnosticResult<'_, Checked<Ast<'_>>> {
//!     parse(expression).and_then_diagnose(check)
//! }
//! ```
//!
//! Here, `and_then_diagnose` is much like the standard `Result::and_then`, but
//! accepts a diagnostic function and preserves any input `Diagnostic`s. Similarly,
//! `map_output` resembles `Result::map`, but instead maps only the output `T` and
//! forwards `Diagnostic`s.
//!
//! `DiagnosticResult`s can be constructed from related types, such as `Result`
//! types of a single error `Diagnostic` or iterators with `Diagnostic` items.
// //! ```rust
// //! fn parse(expression: &str) -> Result<Ast<'_>, ParseError> { ... }
// //!
// //! fn analyze(tree: &Ast) -> impl '_ + Iterator<Item = BoxedDiagnostic<'_>> { ... }
// //!
// //! pub fn parse_and_analyze(expression: &str) -> DiagnosticResult<'_, Ast<'_>> {
// //!     parse(expression)
// //!         .into_error_diagnostic()
// //!         .and_then_diagnose(|tree| analyze(&tree).into_non_error_diagnostic());
// //! }
// //! ```
//!
//! ## Collation

use miette::{Diagnostic, LabeledSpan, Severity, SourceCode};
use mitsein::iter1::{Extend1, FromIterator1, IntoIterator1, Iterator1, IteratorExt as _};
use mitsein::slice1::Slice1;
use mitsein::vec1::Vec1;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::{Chain, Flatten};
use std::option;

pub mod prelude {
    pub use crate::{
        BoxedDiagnosticExt as _, DiagnosticExt as _, DiagnosticResultExt as _, ErrorExt as _,
        IteratorExt as _, ResultExt as _,
    };
}

type Related<'d> = Flatten<option::IntoIter<Box<dyn Iterator<Item = &'d dyn Diagnostic> + 'd>>>;
type HeadAndRelated<'d> = Chain<option::IntoIter<&'d dyn Diagnostic>, Related<'d>>;

/// Extension methods for [`Diagnostic`]s.
pub trait DiagnosticExt: Diagnostic {
    /// Gets a [non-empty iterator][`Iterator1`] over the [`Diagnostic`]'s tree of related
    /// [`Diagnostic`]s.
    ///
    /// [`Diagnostic`]s have zero or more related `Diagnostic`s. The returned iterator successively
    /// calls [`Diagnostic::related`] and walks the tree to yield all related `Diagnostic`s. The
    /// iterator also yields `self`.
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

/// An [`Iterator`] over a [`Diagnostic`]'s tree of related [`Diagnostic`]s.
///
/// See [`DiagnosticExt::tree`].
pub struct Tree<'d> {
    stack: Vec<HeadAndRelated<'d>>,
    related: HeadAndRelated<'d>,
}

impl Debug for Tree<'_> {
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
///
/// See [`ErrorExt::sources`].
#[derive(Debug)]
pub struct Sources<'e> {
    source: Option<&'e dyn error::Error>,
}

impl<'e> Iterator for Sources<'e> {
    type Item = &'e dyn error::Error;

    fn next(&mut self) -> Option<Self::Item> {
        self.source.take().inspect(|next| {
            self.source = next.source();
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

/// A type that can be converted into a shared [`Diagnostic`] trait object through a reference.
pub trait AsDiagnosticObject {
    /// Converts `&self` to a [`Diagnostic`] trait object `&dyn Diagnostic`.
    fn as_diagnostic_object(&self) -> &dyn Diagnostic;
}

impl<D> AsDiagnosticObject for &'_ D
where
    D: AsDiagnosticObject + ?Sized,
{
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        D::as_diagnostic_object(*self)
    }
}

impl AsDiagnosticObject for dyn Diagnostic {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self
    }
}

/// A type that can be converted into a shared [non-empty slice][`Slice1`] of
/// [`AsDiagnosticObject`]s through a reference.
pub trait AsDiagnosticSlice1 {
    /// The diagnostic type of items in the [`Slice1`].
    type Diagnostic: AsDiagnosticObject;

    /// Converts `&self` to a [`Slice1`] of [`AsDiagnosticObject`]s.
    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic>;
}

impl<T> AsDiagnosticSlice1 for &'_ T
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

impl AsDiagnosticObject for BoxedDiagnostic<'_> {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self.as_ref()
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
#[derive(Debug)]
pub struct Diagnosed<'d, T>(pub T, pub Vec<BoxedDiagnostic<'d>>);

impl<'d, T> Diagnosed<'d, T> {
    pub const fn ok(output: T) -> DiagnosticResult<'d, T> {
        Ok(Diagnosed::from_output(output))
    }

    /// Constructs a `Diagnosed` from an output `T` with no [`Diagnostic`]s.
    pub const fn from_output(output: T) -> Self {
        Diagnosed(output, vec![])
    }

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

    pub fn collate(self) -> (T, Option<Collation<Vec1<BoxedDiagnostic<'d>>>>) {
        let Diagnosed(output, diagnostics) = self;
        (
            output,
            Vec1::try_from(diagnostics).ok().map(Collation::from),
        )
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
/// [`Diagnostic`]s serially when formatted.
///
/// See [`DiagnosticResult`].
///
/// # Relation to `Collation`
///
/// Both `Error` and [`Collation`] aggregate one or more [`Diagnostic`]s, but these types are
/// distinct. `Error` is intended for continued aggregation of one or more **error**
/// [`Diagnostic`]s via [`DiagnosticResult`]. `Error` is **not** itself a [`Diagnostic`], but
/// exposes a collection of [`Diagnostic`]s from diagnostic functions. An `Error` [can be
/// converted][`Error::collate`] into a [`Collation`] but not the other way around.
#[derive(Debug)]
#[repr(transparent)]
pub struct Error<'d>(pub Vec1<BoxedDiagnostic<'d>>);

impl<'d> Error<'d> {
    /// Converts from `Error` into its associated [`Diagnostic`]s.
    pub fn into_diagnostics(self) -> Vec1<BoxedDiagnostic<'d>> {
        self.0
    }

    pub fn collate(self) -> Collation<Vec1<BoxedDiagnostic<'d>>> {
        Collation::from(self)
    }

    /// Gets the associated [`Diagnostic`]s of the `Error`.
    pub fn diagnostics(&self) -> &Slice1<BoxedDiagnostic<'d>> {
        self.0.as_slice1()
    }
}

impl Display for Error<'_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self.diagnostics().iter() {
            writeln!(formatter, "{}", diagnostic)?;
        }
        Ok(())
    }
}

impl error::Error for Error<'_> {}

impl<'d> IntoIterator for Error<'d> {
    type IntoIter = <Vec1<BoxedDiagnostic<'d>> as IntoIterator>::IntoIter;
    type Item = BoxedDiagnostic<'d>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl IntoIterator1 for Error<'_> {
    fn into_iter1(self) -> Iterator1<Self::IntoIter> {
        self.0.into_iter1()
    }
}

/// A collated [`Diagnostic`] of one or more related [`Diagnostic`]s.
///
/// `Collation` relates an arbitrary non-empty vector or slice of [`Diagnostic`] trait objects via
/// [`Diagnostic::related`]. The [`Diagnostic`] and [`Error`][`error::Error`] implementations
/// forward to the head and the tail is exposed by [`Diagnostic::related`].
///
/// `Collation` implements [the standard `Error` trait][`error::Error`] and displays its associated
/// [`Diagnostic`]s serially when formatted.
///
/// # Relation to `Error`
///
/// Both `Collation` and [`Error`] aggregate one or more [`Diagnostic`]s, but these types are
/// distinct. `Collation` is itself a [`Diagnostic`] and is intended for relating a collection of
/// otherwise disjoint [`Diagnostic`]s via [`Diagnostic::related`]. This relationship cannot be
/// modified (only nested).
#[repr(transparent)]
pub struct Collation<T>(T);

impl<T> Collation<T>
where
    T: AsDiagnosticSlice1,
{
    fn first(&self) -> &dyn Diagnostic {
        self.0.as_diagnostic_slice1().first().as_diagnostic_object()
    }

    /// Gets an iterator over the codes of the collated [`Diagnostic`]s.
    pub fn codes(&self) -> impl '_ + Iterator<Item = Box<dyn Display + '_>> {
        self.0
            .as_diagnostic_slice1()
            .iter()
            .map(AsDiagnosticObject::as_diagnostic_object)
            .flat_map(Diagnostic::code)
    }

    /// Gets an iterator over the [`Severity`]s of the collated [`Diagnostic`]s.
    pub fn severities(&self) -> impl '_ + Iterator<Item = Severity> {
        self.0
            .as_diagnostic_slice1()
            .iter()
            .map(AsDiagnosticObject::as_diagnostic_object)
            .flat_map(Diagnostic::severity)
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
