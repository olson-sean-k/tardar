//! **Tardar** is a library that provides extensions for the [`miette`] crate. [Diagnostic
//! `Result`][`DiagnosticResult`]s are the primary extension, which pair an output with aggregated
//! [`Diagnostic`]s in both the `Ok` and `Err` variants.
//!
//! [`Diagnostic`]: miette::Diagnostic
//! [`DiagnosticResult`]: crate::DiagnosticResult
//! [`Result`]: std::result::Result
//!
//! [`miette`]: https://crates.io/crates/miette

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use std::cmp;
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

#[derive(Clone, Copy, Debug)]
pub enum EndIndex {
    Closed(usize),
    Intersticial(usize),
}

impl EndIndex {
    pub fn inclusive(self) -> Option<usize> {
        match self {
            EndIndex::Closed(index) => Some(index - 1),
            EndIndex::Intersticial(_) => None,
        }
    }

    pub fn exclusive(self) -> usize {
        match self {
            EndIndex::Closed(index) | EndIndex::Intersticial(index) => index,
        }
    }
}

// TODO: Figure this out. How should zero-width spans be handled?
pub trait Span: Clone + Sized {
    fn from_point_vector(start: usize, len: usize) -> Self;

    fn from_points(start: usize, end: usize) -> Option<Self> {
        (end >= start).then(|| Self::from_point_vector(start, end - start + 1))
    }

    fn converged(offset: usize) -> Self {
        Self::from_point_vector(offset, 1)
    }

    fn start(&self) -> usize;

    fn end(&self) -> EndIndex {
        let index = self.start() + self.len();
        if self.is_intersticial() {
            EndIndex::Intersticial(index)
        }
        else {
            EndIndex::Closed(index)
        }
    }

    fn center(&self) -> usize {
        self.start() + (self.len() / 2)
    }

    fn len(&self) -> usize;

    fn contains(&self, other: &Self) -> bool {
        self.start() <= other.start() && self.end().exclusive() >= other.end().exclusive()
    }

    fn is_intersticial(&self) -> bool {
        self.len() == 0
    }

    fn adjacency(&self, other: &Self) -> Option<Self> {
        let start = cmp::max(self.start(), other.start());
        let end = cmp::min(self.end(), other.end());
        if end < start && end == start - 1 {
            Some(Self::from_point_vector(start, 0))
        }
        else {
            Self::from_points(start, end)
        }
    }

    fn intersection(&self, other: &Self) -> Option<Self> {
        Self::from_points(
            cmp::max(self.start(), other.start()),
            cmp::min(self.end(), other.end()),
        )
    }

    fn union(&self, other: &Self) -> Self {
        Self::from_points(
            cmp::min(self.start(), other.start()),
            cmp::max(self.end(), other.end()),
        )
        .expect("span ")
    }

    fn difference(&self, other: &Self) -> Vec<Self> {
        let mut spans = Vec::with_capacity(2);
        let min = cmp::min(other.start(), other.end());
        if min > self.start() && min < self.end() {
            spans.push((self.start(), min - self.start()).into());
        }
        let max = cmp::max(other.start(), other.end());
        if max < self.end() && max > self.start() {
            spans.push((max + 1, self.end() - max).into());
        }
        spans
    }
}

pub trait SourceSpanExt {
    fn union(&self, other: &SourceSpan) -> SourceSpan;
}

impl SourceSpanExt for SourceSpan {
    fn union(&self, other: &SourceSpan) -> SourceSpan {
        let start = cmp::min(self.offset(), other.offset());
        let end = cmp::max(self.offset() + self.len(), other.offset() + other.len());
        (start, end - start).into()
    }
}

#[derive(Clone, Debug)]
pub struct CompositeSourceSpan {
    label: Option<&'static str>,
    kind: CompositeKind,
}

impl CompositeSourceSpan {
    pub fn span(label: Option<&'static str>, span: SourceSpan) -> Self {
        CompositeSourceSpan {
            label,
            kind: CompositeKind::Span(span),
        }
    }

    pub fn correlated(
        label: Option<&'static str>,
        span: SourceSpan,
        correlated: CorrelatedSourceSpan,
    ) -> Self {
        CompositeSourceSpan {
            label,
            kind: CompositeKind::Correlated { span, correlated },
        }
    }

    pub fn labels(&self) -> Vec<LabeledSpan> {
        let label = self.label.map(str::to_string);
        match self.kind {
            CompositeKind::Span(ref span) => vec![LabeledSpan::new_with_span(label, *span)],
            CompositeKind::Correlated {
                ref span,
                ref correlated,
            } => {
                let mut labels = vec![LabeledSpan::new_with_span(label, *span)];
                labels.extend(correlated.labels());
                labels
            }
        }
    }
}

#[derive(Clone, Debug)]
enum CompositeKind {
    Span(SourceSpan),
    Correlated {
        span: SourceSpan,
        correlated: CorrelatedSourceSpan,
    },
}

#[derive(Clone, Debug)]
pub enum CorrelatedSourceSpan {
    Contiguous(SourceSpan),
    Split(SourceSpan, SourceSpan),
}

impl CorrelatedSourceSpan {
    pub fn split_some(left: Option<SourceSpan>, right: SourceSpan) -> Self {
        if let Some(left) = left {
            CorrelatedSourceSpan::Split(left, right)
        }
        else {
            CorrelatedSourceSpan::Contiguous(right)
        }
    }

    pub fn labels(&self) -> Vec<LabeledSpan> {
        let label = Some("here".to_string());
        match self {
            CorrelatedSourceSpan::Contiguous(ref span) => {
                vec![LabeledSpan::new_with_span(label, *span)]
            }
            CorrelatedSourceSpan::Split(ref left, ref right) => vec![
                LabeledSpan::new_with_span(label.clone(), *left),
                LabeledSpan::new_with_span(label, *right),
            ],
        }
    }
}

impl From<SourceSpan> for CorrelatedSourceSpan {
    fn from(span: SourceSpan) -> Self {
        CorrelatedSourceSpan::Contiguous(span)
    }
}
