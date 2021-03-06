// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use super::location;

/// Wrapper for the types of location information that may be attached to an
/// error message.
#[derive(Clone, PartialEq, Debug)]
pub enum At<L, S> {
    None,
    Location(L),
    Span(S),
}

impl<L, S> std::fmt::Display for At<L, S>
where
    L: std::fmt::Display,
    S: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                At::None => write!(f, "<unknown>"),
                At::Location(l) => write!(f, "{l}"),
                At::Span(s) => write!(f, "{s}"),
            }
        } else {
            match self {
                At::None => Ok(()),
                At::Location(l) => write!(f, " at {l}"),
                At::Span(s) => write!(f, " at {s}"),
            }
        }
    }
}

impl<L, S> At<L, S> {
    pub fn as_ref(&self) -> At<&L, &S> {
        match self {
            At::None => At::None,
            At::Location(l) => At::Location(l),
            At::Span(s) => At::Span(s),
        }
    }

    pub fn is_known(&self) -> bool {
        !matches!(self, At::None)
    }
}

/// Trait that allows error messages to be constructed.
pub trait Error<'i, I>
where
    Self: Fallback,
    I: 'i,
{
    /// The location tracker used to provide location information for the
    /// error messages.
    type LocationTracker: location::Tracker<I>;

    /// Constructor for error messages stating that one of a number of tokens
    /// was expected but another was found. The span corresponds to the token
    /// that was found. None is used for EOF.
    fn expected_found<J>(
        expected: J,
        found: Option<I>,
        at: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self
    where
        J: IntoIterator<Item = Option<I>>;

    /// Adds to the set of expected tokens by means of the given other
    /// expected-found message.
    fn merge_expected_found(&mut self, other: &Self);

    /// Returns whether this error message is an expected-found message that
    /// [Error::merge_expected_found()] can be applied to.
    fn is_expected_found(&self) -> bool;

    /// Returns the location information associated with this error, if any.
    #[allow(clippy::type_complexity)] // I agree, though.
    fn location(
        &self,
    ) -> At<
        &<Self::LocationTracker as location::Tracker<I>>::Location,
        &<Self::LocationTracker as location::Tracker<I>>::Span,
    >;

    /// Constructor for an unmatched left delimiter error.
    fn unmatched_left_delimiter(
        left_token: I,
        left_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        close_before: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self;

    /// Constructor for an unmatched right delimiter error.
    fn unmatched_right_delimiter(
        right_token: I,
        right_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        open_before: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self;

    /// Constructor for an unmatched delimiter type error.
    fn unmatched_delimiter_type(
        left_token: I,
        left_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        right_token: I,
        right_span: <Self::LocationTracker as location::Tracker<I>>::Span,
    ) -> Self;

    /// Constructor for a custom message with a location.
    fn custom<M: ToString>(
        msg: M,
        at: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self;
}

/// Trait that allows fallback error messages to be constructed when no
/// generics are available.
pub trait Fallback {
    /// Constructor for a custom message without location data.
    fn simple<M: ToString>(msg: M) -> Self;
}

/// Error message type that doesn't actually record any error information, just
/// that there was an error.
#[derive(Clone, Debug, PartialEq)]
pub struct Void<I> {
    phantom: std::marker::PhantomData<I>,
}

impl<I> Default for Void<I> {
    fn default() -> Self {
        Self {
            phantom: Default::default(),
        }
    }
}

impl<'i, I> Error<'i, I> for Void<I>
where
    I: 'i,
{
    type LocationTracker = location::Simple;

    fn expected_found<J>(
        _expected: J,
        _found: Option<I>,
        _at: At<usize, std::ops::Range<usize>>,
    ) -> Self
    where
        J: IntoIterator<Item = Option<I>>,
    {
        Self::default()
    }

    fn merge_expected_found(&mut self, _other: &Self) {}

    fn is_expected_found(&self) -> bool {
        false
    }

    fn location(&self) -> At<&usize, &std::ops::Range<usize>> {
        At::None
    }

    fn unmatched_left_delimiter(
        _left_token: I,
        _left_span: std::ops::Range<usize>,
        _close_before: At<usize, std::ops::Range<usize>>,
    ) -> Self {
        Self::default()
    }

    fn unmatched_right_delimiter(
        _right_token: I,
        _right_span: std::ops::Range<usize>,
        _open_before: At<usize, std::ops::Range<usize>>,
    ) -> Self {
        Self::default()
    }

    fn unmatched_delimiter_type(
        _left_token: I,
        _left_span: std::ops::Range<usize>,
        _right_token: I,
        _right_span: std::ops::Range<usize>,
    ) -> Self {
        Self::default()
    }

    fn custom<M: ToString>(_msg: M, _at: At<usize, std::ops::Range<usize>>) -> Self {
        Self::default()
    }
}

impl<I> Fallback for Void<I> {
    fn simple<M: ToString>(_msg: M) -> Self {
        Self::default()
    }
}

/// Simple error message type.
#[derive(Clone, Debug, PartialEq)]
pub enum Simple<I, L = location::Simple>
where
    L: location::Tracker<I>,
    I: Eq + std::hash::Hash,
{
    /// One of .0 was expected, but .1 was found at .2
    ExpectedFound(HashSet<Option<I>>, Option<I>, At<L::Location, L::Span>),

    /// Unmatched left delimiter error.
    UnmatchedLeftDelimiter(I, L::Span, At<L::Location, L::Span>),

    /// Unmatched right delimiter error.
    UnmatchedRightDelimiter(I, L::Span, At<L::Location, L::Span>),

    /// Unmatched delimiter type error.
    UnmatchedDelimiterType(I, L::Span, I, L::Span),

    /// Custom error message.
    Custom(String, At<L::Location, L::Span>),
}

impl<'i, I, L> Error<'i, I> for Simple<I, L>
where
    I: 'i + Eq + std::hash::Hash + Clone,
    L: location::Tracker<I>,
{
    type LocationTracker = L;

    fn expected_found<J>(expected: J, found: Option<I>, at: At<L::Location, L::Span>) -> Self
    where
        J: IntoIterator<Item = Option<I>>,
    {
        Self::ExpectedFound(expected.into_iter().collect(), found, at)
    }

    fn merge_expected_found(&mut self, other: &Self) {
        if let (Self::ExpectedFound(dest, _, _), Self::ExpectedFound(src, _, _)) = (self, other) {
            dest.extend(src.iter().cloned())
        }
    }

    fn is_expected_found(&self) -> bool {
        matches!(self, Self::ExpectedFound(_, _, _))
    }

    fn location(&self) -> At<&L::Location, &L::Span> {
        match self {
            Simple::ExpectedFound(_, _, l) => l.as_ref(),
            Simple::UnmatchedLeftDelimiter(_, _, l) => l.as_ref(),
            Simple::UnmatchedRightDelimiter(_, _, l) => l.as_ref(),
            Simple::UnmatchedDelimiterType(_, _, _, s) => At::Span(s),
            Simple::Custom(_, l) => l.as_ref(),
        }
    }

    fn unmatched_left_delimiter(
        left_token: I,
        left_span: L::Span,
        close_before: At<L::Location, L::Span>,
    ) -> Self {
        Simple::UnmatchedLeftDelimiter(left_token, left_span, close_before)
    }

    fn unmatched_right_delimiter(
        right_token: I,
        right_span: L::Span,
        open_before: At<L::Location, L::Span>,
    ) -> Self {
        Simple::UnmatchedRightDelimiter(right_token, right_span, open_before)
    }

    fn unmatched_delimiter_type(
        left_token: I,
        left_span: L::Span,
        right_token: I,
        right_span: L::Span,
    ) -> Self {
        Simple::UnmatchedDelimiterType(left_token, left_span, right_token, right_span)
    }

    fn custom<M: ToString>(msg: M, at: At<L::Location, L::Span>) -> Self {
        Self::Custom(msg.to_string(), at)
    }
}

impl<'i, I, L> Fallback for Simple<I, L>
where
    L: location::Tracker<I>,
    I: Eq + std::hash::Hash,
{
    fn simple<M: ToString>(msg: M) -> Self {
        Self::Custom(msg.to_string(), At::None)
    }
}

impl<'i, I, L> std::fmt::Display for Simple<I, L>
where
    L: location::Tracker<I>,
    I: std::fmt::Display + Eq + std::hash::Hash,
    L::Location: std::fmt::Display,
    L::Span: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Simple::ExpectedFound(expected, found, at) => {
                let expected: Vec<_> = expected
                    .iter()
                    .map(|x| match x {
                        Some(x) => x.to_string(),
                        None => String::from("EOF"),
                    })
                    .collect();
                match expected.len() {
                    0 => write!(f, "found unexpected")?,
                    1 => write!(f, "expected {} but found", expected[0])?,
                    2 => write!(f, "expected {} or {} but found", expected[0], expected[1])?,
                    _ => {
                        write!(f, "expected {}", expected[0])?;
                        for expected in &expected[1..expected.len() - 1] {
                            write!(f, ", {}", expected)?;
                        }
                        write!(f, ", or {} but found", expected[expected.len() - 1])?;
                    }
                };
                match found {
                    Some(x) => write!(f, " {x}")?,
                    None => write!(f, " EOF")?,
                };
                write!(f, "{at}")
            }
            Simple::UnmatchedLeftDelimiter(lt, ls, before) => {
                write!(f, "unmatched left {lt} ({ls})")?;
                if before.is_known() {
                    write!(f, "; must be closed before {before}")?;
                }
                Ok(())
            }
            Simple::UnmatchedRightDelimiter(rt, rs, after) => {
                write!(f, "unmatched right {rt} ({rs})")?;
                if after.is_known() {
                    write!(f, "; must be opened after {after}")?;
                }
                Ok(())
            }
            Simple::UnmatchedDelimiterType(lt, ls, rt, rs) => {
                write!(f, "left {lt} ({ls}) does not match right {rt} ({rs})")
            }
            Simple::Custom(msg, at) => {
                write!(f, "{msg}{at}")
            }
        }
    }
}
