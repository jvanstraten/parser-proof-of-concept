// SPDX-License-Identifier: Apache-2.0

use std::{borrow::Borrow, collections::HashSet};

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
pub trait Error<'i, H, I>
where
    Self: Fallback,
    H: Borrow<I> + Clone + 'i,
    I: 'i,
{
    /// The location tracker used to provide location information for the
    /// error messages.
    type LocationTracker: location::Tracker<I>;

    /// Constructor for error messages stating that one of a number of tokens
    /// was expected but another was found. The span corresponds to the token
    /// that was found. None is used for EOF.
    fn expected_found<G>(
        expected: G,
        found: Option<H>,
        at: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self
    where
        G: IntoIterator<Item = Option<H>>,
        G::IntoIter: 'i;

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
        left_token: H,
        left_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        close_before: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self;

    /// Constructor for an unmatched right delimiter error.
    fn unmatched_right_delimiter(
        right_token: H,
        right_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        open_before: At<
            <Self::LocationTracker as location::Tracker<I>>::Location,
            <Self::LocationTracker as location::Tracker<I>>::Span,
        >,
    ) -> Self;

    /// Constructor for an unmatched delimiter type error.
    fn unmatched_delimiter_type(
        left_token: H,
        left_span: <Self::LocationTracker as location::Tracker<I>>::Span,
        right_token: H,
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

/// Simple error message type.
#[derive(Clone, Debug, PartialEq)]
pub enum Simple<H, I, L = location::Simple>
where
    L: location::Tracker<I>,
    H: Borrow<I> + Clone + Eq + std::hash::Hash,
{
    /// One of .0 was expected, but .1 was found at .2
    ExpectedFound(HashSet<Option<H>>, Option<H>, At<L::Location, L::Span>),

    /// Unmatched left delimiter error.
    UnmatchedLeftDelimiter(H, L::Span, At<L::Location, L::Span>),

    /// Unmatched right delimiter error.
    UnmatchedRightDelimiter(H, L::Span, At<L::Location, L::Span>),

    /// Unmatched delimiter type error.
    UnmatchedDelimiterType(H, L::Span, H, L::Span),

    /// Custom error message.
    Custom(String, At<L::Location, L::Span>),
}

impl<'i, H, I, L> Error<'i, H, I> for Simple<H, I, L>
where
    H: 'i + Borrow<I> + Clone + Eq + std::hash::Hash,
    I: 'i,
    L: location::Tracker<I>,
{
    type LocationTracker = L;

    fn expected_found<J>(expected: J, found: Option<H>, at: At<L::Location, L::Span>) -> Self
    where
        J: IntoIterator<Item = Option<H>>,
        J::IntoIter: 'i,
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
        left_token: H,
        left_span: L::Span,
        close_before: At<L::Location, L::Span>,
    ) -> Self {
        Simple::UnmatchedLeftDelimiter(left_token, left_span, close_before)
    }

    fn unmatched_right_delimiter(
        right_token: H,
        right_span: L::Span,
        open_before: At<L::Location, L::Span>,
    ) -> Self {
        Simple::UnmatchedRightDelimiter(right_token, right_span, open_before)
    }

    fn unmatched_delimiter_type(
        left_token: H,
        left_span: L::Span,
        right_token: H,
        right_span: L::Span,
    ) -> Self {
        Simple::UnmatchedDelimiterType(left_token, left_span, right_token, right_span)
    }

    fn custom<M: ToString>(msg: M, at: At<L::Location, L::Span>) -> Self {
        Self::Custom(msg.to_string(), at)
    }
}

impl<'i, H, I, L> Fallback for Simple<H, I, L>
where
    H: Borrow<I> + Clone + Eq + std::hash::Hash + 'i,
    L: location::Tracker<I>,
{
    fn simple<M: ToString>(msg: M) -> Self {
        Self::Custom(msg.to_string(), At::None)
    }
}

impl<'i, H, I, L> std::fmt::Display for Simple<H, I, L>
where
    H: Borrow<I> + Clone + Eq + std::hash::Hash + 'i,
    I: std::fmt::Display + Eq + std::hash::Hash,
    L: location::Tracker<I>,
    L::Location: std::fmt::Display,
    L::Span: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Simple::ExpectedFound(expected, found, at) => {
                let expected: Vec<_> = expected
                    .iter()
                    .map(|x| match x {
                        Some(x) => x.borrow().to_string(),
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
                    Some(x) => write!(f, " {}", x.borrow())?,
                    None => write!(f, " EOF")?,
                };
                write!(f, "{at}")
            }
            Simple::UnmatchedLeftDelimiter(lt, ls, before) => {
                write!(f, "unmatched left {} ({ls})", lt.borrow())?;
                if before.is_known() {
                    write!(f, "; must be closed before {before}")?;
                }
                Ok(())
            }
            Simple::UnmatchedRightDelimiter(rt, rs, after) => {
                write!(f, "unmatched right {} ({rs})", rt.borrow())?;
                if after.is_known() {
                    write!(f, "; must be opened after {after}")?;
                }
                Ok(())
            }
            Simple::UnmatchedDelimiterType(lt, ls, rt, rs) => {
                write!(
                    f,
                    "left {} ({ls}) does not match right {} ({rs})",
                    lt.borrow(),
                    rt.borrow()
                )
            }
            Simple::Custom(msg, at) => {
                write!(f, "{msg}{at}")
            }
        }
    }
}
