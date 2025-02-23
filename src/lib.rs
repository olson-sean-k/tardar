//! **Tardar** is a Rust library that provides extensions for the [`miette`] crate. These
//! extensions primarily provide more ergonomic diagnostic `Result`s and collation of
//! `Diagnostic`s.
//!
//! ## Diagnostic Results
//!
//! [`DiagnosticResult`] is a [`Result`] type that accumulates and associates [`Diagnostic`]s with
//! an output type `T` for both success and failure (`Ok` and `Err` variants). The `Ok` variant
//! contains a [`Diagnosed`] with a `T` and **zero or more** non-error [`Diagnostic`]s. The `Err`
//! variant contains an [`Error`] with **one or more** [`Diagnostic`]s, at least one of which is
//! considered an error.
//!
//! Together with extension methods, [`DiagnosticResult`] supports fluent and ergonomic composition
//! of **diagnostic functions**. Here, a diagnostic function is one that returns a
//! [`DiagnosticResult`] or other container of [`Diagnostic`]s. For example, a library that parses
//! a data structure or language from text may use diagnostic functions for parsing and analysis.
//!
//! ```rust
//! use tardar::DiagnosticResult;
//!
//! # struct Checked<T>(T);
//! # struct Ast<'x>(&'x str);
//! #
//! /// Parses an expression into an abstract syntax tree (AST).
//! fn parse(expression: &str) -> DiagnosticResult<Ast<'_>> {
//! #     tardar::Diagnosed::ok(Ast(expression)) /*
//!     ...
//! # */
//! }
//!
//! /// Checks an AST for token, syntax, and rule correctness.
//! fn check<'x>(tree: Ast<'x>) -> DiagnosticResult<Checked<Ast<'x>>> {
//! #     tardar::Diagnosed::ok(Checked(tree)) /*
//!     ...
//! # */
//! }
//! ```
//!
//! These diagnostic functions can be composed with extension methods.
//!
//! ```rust
//! use tardar::prelude::*;
//! use tardar::DiagnosticResult;
//!
//! # struct Checked<T>(T);
//! # struct Ast<'x>(&'x str);
//! #
//! # fn parse(expression: &str) -> DiagnosticResult<Ast<'_>> {
//! #     tardar::Diagnosed::ok(Ast(expression))
//! # }
//! #
//! # fn check<'x>(tree: Ast<'x>) -> DiagnosticResult<Checked<Ast<'x>>> {
//! #     tardar::Diagnosed::ok(Checked(tree))
//! # }
//! #
//! /// Parses an expression into a checked AST.
//! pub fn parse_and_check(expression: &str) -> DiagnosticResult<Checked<Ast<'_>>> {
//!     parse(expression).and_then_diagnose(check)
//! }
//! ```
//!
//! The `parse_and_check` function forwards the output of `parse` to `check` with
//! [`and_then_diagnose`][`DiagnosticResultExt::and_then_diagnose`]. This function is much like the
//! standard [`Result::and_then`], but accepts a diagnostic function and so preserves any input
//! [`Diagnostic`]s. **If `parse` succeeds with some warnings but `check` fails with an error, then
//! the output [`Error`] will contain both the warning and error [`Diagnostic`]s.**
//!
//! Other shapes of diagnostic functions can also be composed. For example, an analysis function
//! may accept a shared reference and return an iterator rather than a result, since it cannot
//! conceptually fail.
//!
//! ```rust
//! use tardar::BoxedDiagnostic;
//!
//! # struct Checked<T>(T);
//! # struct Ast<'x>(&'x str);
//! #
//! /// Analyzes a checked AST and returns non-error diagnostics.
//! fn analyze<'x>(tree: &Checked<Ast<'x>>) -> impl Iterator<Item = BoxedDiagnostic> {
//! #     Option::<_>::None.into_iter() /*
//!     ...
//! # */
//! }
//! ```
//!
//! This diagnostic function can too be composed into `parse_and_check` using extension methods.
//!
//! ```rust
//! use tardar::prelude::*;
//! use tardar::{BoxedDiagnostic, DiagnosticResult};
//!
//! # struct Checked<T>(T);
//! # struct Ast<'x>(&'x str);
//! #
//! # fn parse(expression: &str) -> DiagnosticResult<Ast<'_>> {
//! #     tardar::Diagnosed::ok(Ast(expression))
//! # }
//! #
//! # fn check<'x>(tree: Ast<'x>) -> DiagnosticResult<Checked<Ast<'x>>> {
//! #     tardar::Diagnosed::ok(Checked(tree))
//! # }
//! #
//! # fn analyze<'x>(tree: &Checked<Ast<'x>>) -> impl Iterator<Item = BoxedDiagnostic> {
//! #     Option::<_>::None.into_iter()
//! # }
//! #
//! /// Parses an expression into a checked AST with analysis.
//! pub fn parse_and_check(expression: &str) -> DiagnosticResult<Checked<Ast<'_>>> {
//!     parse(expression)
//!         .and_then_diagnose(check)
//!         .diagnose_non_errors(analyze)
//! }
//! ```
//!
//! The output of `check` is forwarded to `analyze` with
//! [`diagnose_non_errors`][`DiagnosticResult::diagnose_non_errors`]. This function is more bespoke
//! and accepts a diagnostic function that itself accepts the output `T` by shared reference. Any
//! [`Diagnostic`]s returned by the accepted function are interpreted as non-errors and are
//! accumulated into the [`Diagnosed`].
//!
//! [`DiagnosticResult`]s can be constructed from related types, such as singular [`Result`] types
//! and iterators with [`Diagnostic`] items. When extension functions like `and_then_diagnose` are
//! not immediately compatible, it is often possible to perform conversions in a closure.
//!
//! ## Collation
//!
//! [`miette`] primarily groups [`Diagnostic`]s via [`Diagnostic::related`]. However, it can be
//! inflexible or cumbersome to provide such an implementation and [`Diagnostic`]s are commonly and
//! more easily organized into collections or iterators. [`Collation`] is a [`Diagnostic`] type
//! that relates arbitrary [**non-empty** vectors][`Vec1`] and [slices][`Slice1`] of
//! [`Diagnostic`]s.
//!
//! ```rust
//! use tardar::{Diagnosed, DiagnosticResult, OwnedCollation};
//!
//! # struct Client;
//! # struct Bssid;
//! # struct ActiveScan;
//! #
//! /// Performs an active scan for the given BSSID.
//! pub fn scan(
//!     client: &Client,
//!     bssid: Bssid,
//! ) -> Result<ActiveScan, OwnedCollation> {
//!     let result: DiagnosticResult<ActiveScan> = {
//! #         Diagnosed::ok(ActiveScan) /*
//!         ...
//! # */
//!     };
//!     // The try operator `?` can be used here, because `Error` can be converted into
//!     // `Collation`. If the result is `Err`, then the `Collation` relates the error diagnostics.
//!     let scan = result.map(Diagnosed::into_output)?;
//! # /*
//!     ...
//! # */
//! #     Ok(scan)
//! }
//! ```
//!
//! Note that [`DiagnosticResult`]s accumulate [`Diagnostic`]s, but do not **relate** them by
//! design: neither [`Diagnosed`] nor [`Error`] implement [`Diagnostic`].

use miette::{Diagnostic, LabeledSpan, Severity, SourceCode};
use mitsein::borrow1::CowSlice1;
use mitsein::boxed1::BoxedSlice1;
use mitsein::iter1::{Extend1, FromIterator1, IntoIterator1, Iterator1, IteratorExt as _};
use mitsein::slice1::Slice1;
use mitsein::sync1::ArcSlice1;
use mitsein::vec1::Vec1;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::{Chain, Flatten};
use std::option;
use std::sync::Arc;

pub mod prelude {
    pub use crate::{
        BoxedDiagnosticExt as _, DiagnosticExt as _, DiagnosticResultExt as _, ErrorExt as _,
        IteratorExt as _, ResultExt as _,
    };
}

type Related<'d> = Flatten<option::IntoIter<Box<dyn Iterator<Item = &'d dyn Diagnostic> + 'd>>>;
type HeadAndRelated<'d> = Chain<option::IntoIter<&'d dyn Diagnostic>, Related<'d>>;

/// Extension methods for [`Diagnostic`] types.
pub trait DiagnosticExt: Diagnostic {
    /// Gets a [non-empty iterator][`Iterator1`] over the [`Diagnostic`]'s tree of related
    /// [`Diagnostic`]s.
    ///
    /// [`Diagnostic`]s have zero or more related `Diagnostic`s. The returned iterator successively
    /// calls [`Diagnostic::related`] and walks the tree to yield all related `Diagnostic`s. **The
    /// iterator also yields `self`.**
    fn tree(&self) -> Iterator1<Tree<'_>>;
}

impl<D> DiagnosticExt for D
where
    D: Diagnostic,
{
    fn tree(&self) -> Iterator1<Tree<'_>> {
        // SAFETY: This `Tree` iterator must yield one or more items. `self` is pushed onto the
        //         stack and is popped and yielded in the `Iterator` implementation for `Tree`, so
        //         this `Tree` iterator always yields `self` and therefore one or more items.
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

/// An [`Iterator`] over a tree of related [`Diagnostic`]'s.
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

/// Extension methods for [`Error`][`error::Error`] types.
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

/// Extension methods for [`Iterator`] types.
pub trait IteratorExt: Iterator {
    /// Converts from an [`Iterator`] type of [`AsDiagnosticObject`] items into a non-error
    /// `DiagnosticResult<(), Self::Item>`.
    ///
    /// The [`Diagnostic`] items of the iterator are interpreted as non-errors. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`]s may have error-level severities
    /// despite being interpreted as non-errors.
    fn into_non_error_diagnostic(self) -> DiagnosticResult<(), Self::Item>
    where
        Self: Sized,
        Self::Item: AsDiagnosticObject;

    /// Converts from an [`Iterator`] type of [`AsDiagnosticObject`] items into
    /// `DiagnosticResult<(), Self::Item>` by [`Severity`].
    ///
    /// If any [`Diagnostic`] item has an [error `Severity`][`Severity::Error`], then the items are
    /// interpreted as errors. Otherwise, the items are interpreted as non-errors.
    fn into_diagnostic_by_severity(self) -> DiagnosticResult<(), Self::Item>
    where
        Self: Sized,
        Self::Item: AsDiagnosticObject;
}

impl<I> IteratorExt for I
where
    I: Iterator,
{
    fn into_non_error_diagnostic(self) -> DiagnosticResult<(), Self::Item>
    where
        Self: Sized,
        Self::Item: AsDiagnosticObject,
    {
        Ok(Diagnosed((), self.collect()))
    }

    fn into_diagnostic_by_severity(self) -> DiagnosticResult<(), Self::Item>
    where
        Self: Sized,
        Self::Item: AsDiagnosticObject,
    {
        let diagnostics: Vec<_> = self.collect();
        match Vec1::try_from(diagnostics) {
            Ok(diagnostics) => {
                if diagnostics
                    .iter()
                    .map(AsDiagnosticObject::as_diagnostic_object)
                    .flat_map(Diagnostic::severity)
                    .any(|severity| matches!(severity, Severity::Error))
                {
                    Err(Error(diagnostics))
                }
                else {
                    Ok(Diagnosed((), diagnostics.into()))
                }
            }
            _ => Diagnosed::ok(()),
        }
    }
}

/// Extension methods for [`Iterator1`].
pub trait Iterator1Ext<I>: Sized {
    /// Converts from an [`Iterator1`] of [`AsDiagnosticObject`] items into
    /// `DiagnosticResult<(), I::Item>`.
    ///
    /// The [`Diagnostic`] items of the iterator are interpreted as errors. Note that the
    /// [`Severity`] is not examined and so the [`Diagnostic`]s may have non-error severities
    /// despite being interpreted as errors.
    ///
    /// To interpret the items as non-errors, first convert the [`Iterator1`] into an iterator and
    /// then use [`into_non_error_diagnostic`][`IteratorExt::into_non_error_diagnostic`].
    fn into_error_diagnostic(self) -> DiagnosticResult<(), I::Item>
    where
        I: Iterator + Sized,
        I::Item: AsDiagnosticObject;
}

impl<I> Iterator1Ext<I> for Iterator1<I> {
    fn into_error_diagnostic(self) -> DiagnosticResult<(), I::Item>
    where
        I: Iterator + Sized,
        I::Item: AsDiagnosticObject,
    {
        Err(Error(self.collect1()))
    }
}

/// Extension methods for [`Result`].
pub trait ResultExt<T, E> {
    /// Converts from `Result<T, E>` into `DiagnosticResult<T, E>`.
    ///
    /// The error type `E` must be convertible to a [`Diagnostic`] trait object and is interpreted
    /// as an error. Note that the [`Severity`] is not examined and so the [`Diagnostic`] may have
    /// a non-error severity despite being interpreted as an error.
    fn into_error_diagnostic(self) -> DiagnosticResult<T, E>
    where
        E: AsDiagnosticObject;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_error_diagnostic(self) -> DiagnosticResult<T, E>
    where
        E: AsDiagnosticObject,
    {
        match self {
            Ok(output) => Ok(Diagnosed(output, vec![])),
            Err(error) => Err(Error(Vec1::from_one(error))),
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

impl<D> AsDiagnosticObject for &'_ mut D
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

impl AsDiagnosticObject for Arc<dyn Diagnostic> {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self.as_ref()
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

impl<D> AsDiagnosticSlice1 for ArcSlice1<D>
where
    D: AsDiagnosticObject,
{
    type Diagnostic = D;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        self.as_ref()
    }
}

impl<D> AsDiagnosticSlice1 for BoxedSlice1<D>
where
    D: AsDiagnosticObject,
{
    type Diagnostic = D;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        self.as_ref()
    }
}

impl<D> AsDiagnosticSlice1 for CowSlice1<'_, D>
where
    D: AsDiagnosticObject + Clone,
{
    type Diagnostic = D;

    fn as_diagnostic_slice1(&self) -> &Slice1<Self::Diagnostic> {
        self.as_ref()
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

pub type BoxedDiagnostic = Box<dyn Diagnostic>;

/// Extension methods for [`BoxedDiagnostic`].
pub trait BoxedDiagnosticExt {
    /// Constructs a [`BoxedDiagnostic`] from a [`Diagnostic`].
    fn from_diagnostic<D>(diagnostic: D) -> Self
    where
        D: 'static + Diagnostic;
}

impl BoxedDiagnosticExt for BoxedDiagnostic {
    fn from_diagnostic<D>(diagnostic: D) -> Self
    where
        D: 'static + Diagnostic,
    {
        Box::new(diagnostic) as Box<dyn Diagnostic>
    }
}

impl AsDiagnosticObject for BoxedDiagnostic {
    fn as_diagnostic_object(&self) -> &dyn Diagnostic {
        self.as_ref()
    }
}

/// `Result` that includes [`Diagnostic`]s on both success and failure.
///
/// On success, the `Ok` variant contains a [`Diagnosed`] with **zero or more** diagnostics and an
/// output `T`. On failure, the `Err` variant contains an [`Error`] with **one or more**
/// diagnostics, where at least one of the diagnostics has been interpreted as an error.
pub type DiagnosticResult<T, D = BoxedDiagnostic> = Result<Diagnosed<T, D>, Error<D>>;

/// Extension methods for [`DiagnosticResult`].
pub trait DiagnosticResultExt<T, D> {
    /// Converts from `DiagnosticResult<T, D>` into `Option<T>`.
    ///
    /// This function is similar to [`Result::ok`], but gets only the output `T` from the
    /// [`Diagnosed`] in the `Ok` variant, **discarding any [`Diagnostic`]s**.
    fn ok_output(self) -> Option<T>;

    /// Maps `DiagnosticResult<T, D>` into `DiagnosticResult<U, D>` by applying a function over the
    /// output `T` of the `Ok` variant.
    ///
    /// This function is similar to [`Result::map`], but maps only the non-diagnostic output `T`
    /// from the `Ok` variant in [`DiagnosticResult`], ignoring diagnostics.
    fn map_output<U, F>(self, f: F) -> DiagnosticResult<U, D>
    where
        F: FnOnce(T) -> U;

    /// Calls the given non-error diagnostic function if the `DiagnosticResult` is `Ok` and
    /// otherwise returns the `Err` variant of the `DiagnosticResult`.
    ///
    /// Unlike [`and_then_diagnose`], the given function accepts the output `T` by shared reference
    /// and returns zero or more non-error [`Diagnostic`]s and so cannot itself invoke an error.
    /// These [`Diagnostic`]s are accumulated into the [`Diagnosed`].
    fn diagnose_non_errors<I, F>(self, f: F) -> Self
    where
        I: IntoIterator<Item = D>,
        F: FnOnce(&T) -> I;

    /// Calls the given diagnostic function if the `DiagnosticResult` is `Ok` and otherwise returns
    /// the `Err` variant of the `DiagnosticResult`.
    ///
    /// This function is similar to [`Result::and_then`], but additionally forwards and collects
    /// diagnostics.
    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<U, D>
    where
        F: FnOnce(T) -> DiagnosticResult<U, D>;

    /// Gets an iterator over the associated [`Diagnostic`]s as trait objects.
    fn diagnostics(&self) -> impl '_ + Iterator<Item = &'_ dyn Diagnostic>;

    /// Gets a slice over the associated [`Diagnostic`]s.
    fn as_diagnostic_slice(&self) -> &[D];

    /// Returns `true` if the `DiagnosticResult` has one or more associated [`Diagnostic`]s.
    fn has_diagnostics(&self) -> bool;
}

impl<T, D> DiagnosticResultExt<T, D> for DiagnosticResult<T, D>
where
    D: AsDiagnosticObject,
{
    fn ok_output(self) -> Option<T> {
        match self {
            Ok(Diagnosed(output, _)) => Some(output),
            _ => None,
        }
    }

    fn map_output<U, F>(self, f: F) -> DiagnosticResult<U, D>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(diagnosed) => Ok(diagnosed.map_output(f)),
            Err(error) => Err(error),
        }
    }

    fn diagnose_non_errors<I, F>(self, f: F) -> Self
    where
        I: IntoIterator<Item = D>,
        F: FnOnce(&T) -> I,
    {
        match self {
            Ok(diagnosed) => Ok(diagnosed.diagnose_non_errors(f)),
            Err(error) => Err(error),
        }
    }

    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<U, D>
    where
        F: FnOnce(T) -> DiagnosticResult<U, D>,
    {
        match self {
            Ok(diagnosed) => diagnosed.and_then_diagnose(f),
            Err(diagnostics) => Err(diagnostics),
        }
    }

    fn diagnostics(&self) -> impl '_ + Iterator<Item = &'_ dyn Diagnostic> {
        self.as_diagnostic_slice()
            .iter()
            .map(AsDiagnosticObject::as_diagnostic_object)
    }

    fn as_diagnostic_slice(&self) -> &[D] {
        match self {
            Ok(ref diagnosed) => diagnosed.as_diagnostic_slice(),
            Err(ref error) => error.as_diagnostic_slice1(),
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
/// sense, non-error merely means here that no associated [`Diagnostic`]s prevented the
/// construction of the output `T`. The [`Severity`] of the associated [`Diagnostic`]s is
/// arbitrary.
///
/// See [`DiagnosticResult`].
#[derive(Debug)]
pub struct Diagnosed<T, D = BoxedDiagnostic>(pub T, pub Vec<D>);

impl<T, D> Diagnosed<T, D>
where
    D: AsDiagnosticObject,
{
    /// Constructs a [`DiagnosticResult`] from an output `T` with no [`Diagnostic`]s.
    pub const fn ok(output: T) -> DiagnosticResult<T, D> {
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
    pub fn into_diagnostics(self) -> Vec<D> {
        self.1
    }

    /// Maps `Diagnosed<T, D>` into `Diagnosed<U, D>` by applying a function over the output `T`.
    pub fn map_output<U, F>(self, f: F) -> Diagnosed<U, D>
    where
        F: FnOnce(T) -> U,
    {
        let Diagnosed(output, diagnostics) = self;
        Diagnosed(f(output), diagnostics)
    }

    /// Calls the given non-error diagnostic function with a shared reference to the output `T` and
    /// accumulates any returned [`Diagnostic`]s.
    pub fn diagnose_non_errors<I, F>(self, f: F) -> Self
    where
        I: IntoIterator<Item = D>,
        F: FnOnce(&T) -> I,
    {
        let Diagnosed(output, mut diagnostics) = self;
        diagnostics.extend(f(&output));
        Diagnosed(output, diagnostics)
    }

    /// Calls the given diagnostic function with the output `T` and accumulates [`Diagnostic`]s
    /// into a [`DiagnosticResult`].
    pub fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<U, D>
    where
        F: FnOnce(T) -> DiagnosticResult<U, D>,
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

    /// Converts the `Diagnosed` into the output `T` and a [`Collation`] of any associated
    /// [`Diagnostic`]s.
    pub fn collate(self) -> (T, Option<OwnedCollation<D>>) {
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

    /// Gets an iterator over the associated [`Diagnostic`]s as trait objects.
    pub fn diagnostics(&self) -> impl '_ + Iterator<Item = &'_ dyn Diagnostic> {
        self.1.iter().map(AsDiagnosticObject::as_diagnostic_object)
    }

    /// Gets a slice over the associated [`Diagnostic`]s.
    pub fn as_diagnostic_slice(&self) -> &[D] {
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
/// Both `Error` and [`Collation`] accumulate one or more [`Diagnostic`]s, but these types are
/// distinct. `Error` is intended for continued accumulation of one or more **error**
/// [`Diagnostic`]s via [`DiagnosticResult`]. `Error` is **not** itself a [`Diagnostic`], but
/// exposes a collection of [`Diagnostic`]s from diagnostic functions. An `Error` [can be
/// converted][`Error::collate`] into a [`Collation`] but not the other way around.
#[repr(transparent)]
pub struct Error<D = BoxedDiagnostic>(pub Vec1<D>);

impl<D> Error<D>
where
    D: AsDiagnosticObject,
{
    /// Converts from `Error` into its [`Diagnostic`]s.
    pub fn into_diagnostics(self) -> Vec1<D> {
        self.0
    }

    /// Converts the `Error` into a [`Collation`] of its [`Diagnostic`]s.
    pub fn collate(self) -> OwnedCollation<D> {
        Collation::from(self)
    }

    /// Gets a non-empty iterator over the [`Diagnostic`]s as trait objects.
    pub fn diagnostics(&self) -> Iterator1<impl '_ + Iterator<Item = &'_ dyn Diagnostic>> {
        self.0.iter1().map(AsDiagnosticObject::as_diagnostic_object)
    }

    /// Gets a non-empty slice over the [`Diagnostic`]s.
    pub fn as_diagnostic_slice1(&self) -> &Slice1<D> {
        self.0.as_slice1()
    }
}

impl<D> Debug for Error<D>
where
    D: AsDiagnosticObject,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.debug_tuple("Error").field(&"..").finish()
    }
}

impl<D> Display for Error<D>
where
    D: AsDiagnosticObject,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        for diagnostic in self.diagnostics() {
            writeln!(formatter, "{}", diagnostic)?;
        }
        Ok(())
    }
}

impl<D> error::Error for Error<D> where D: AsDiagnosticObject {}

impl<D> IntoIterator for Error<D>
where
    D: AsDiagnosticObject,
{
    type IntoIter = <Vec1<D> as IntoIterator>::IntoIter;
    type Item = D;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<D> IntoIterator1 for Error<D>
where
    D: AsDiagnosticObject,
{
    fn into_iter1(self) -> Iterator1<Self::IntoIter> {
        self.0.into_iter1()
    }
}

/// An owned [`Collation`].
pub type OwnedCollation<D = BoxedDiagnostic> = Collation<Vec1<D>>;

/// A borrowed [`Collation`].
pub type BorrowedCollation<'c, D = BoxedDiagnostic> = Collation<&'c Slice1<D>>;

/// A copy-on-write [`Collation`].
pub type CowCollation<'c, D = BoxedDiagnostic> = Collation<CowSlice1<'c, D>>;

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
/// Both `Collation` and [`Error`] accumulate one or more [`Diagnostic`]s, but these types are
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

impl<D> Collation<CowSlice1<'_, D>>
where
    D: AsDiagnosticObject + Clone,
{
    pub fn into_owned(self) -> Collation<CowSlice1<'static, D>> {
        Collation(self.0.into_owned().into())
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

impl<'c, D> From<Collation<CowSlice1<'c, D>>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject + Clone,
{
    fn from(collation: Collation<CowSlice1<'c, D>>) -> Self {
        Collation::from(collation.0.into_owned())
    }
}

impl<'c, D> From<Collation<&'c Slice1<D>>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject + Clone,
{
    fn from(collation: Collation<&'c Slice1<D>>) -> Self {
        Collation::from(collation.0.to_vec1())
    }
}

impl<D> From<Error<D>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject,
{
    fn from(error: Error<D>) -> Self {
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

impl<T, D> TryFrom<Diagnosed<T, D>> for Collation<Vec1<D>>
where
    D: AsDiagnosticObject,
{
    type Error = Diagnosed<T, D>;

    fn try_from(diagnosed: Diagnosed<T, D>) -> Result<Self, Self::Error> {
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
