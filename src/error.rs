use std::collections::HashSet;

use super::location;

/// Wrapper for the types of location information that may be attached to an
/// error message.
#[derive(PartialEq)]
pub enum At<L, S>
where
    L: PartialEq,
    S: PartialEq,
{
    None,
    Location(L),
    Span(S),
}

impl<L, S> At<L, S>
where
    L: PartialEq,
    S: PartialEq,
{
    pub fn as_ref(&self) -> At<&L, &S> {
        match self {
            At::None => At::None,
            At::Location(l) => At::Location(l),
            At::Span(s) => At::Span(s),
        }
    }
}

impl<L, S> std::fmt::Display for At<L, S>
where
    L: std::fmt::Display + PartialEq,
    S: std::fmt::Display + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            At::None => Ok(()),
            At::Location(l) => write!(f, " at {l}"),
            At::Span(s) => write!(f, " at {s}"),
        }
    }
}

/// Trait that allows error messages to be constructed.
pub trait Error<'i, I, L>
where
    Self: Fallback,
    I: 'i,
    L: location::LocationTracker<I>,
{
    /// Constructor for error messages stating that one of a number of tokens
    /// was expected but another was found. The span corresponds to the token
    /// that was found. None is used for EOF.
    fn expected_found<J>(expected: J, found: Option<&'i I>, at: At<L::Location, L::Span>) -> Self
    where
        J: IntoIterator<Item = Option<&'i I>>,
        J::IntoIter: 'i;

    /// Adds to the set of expected tokens by means of the given other
    /// expected-found message.
    fn merge_expected_found(&mut self, other: &Self);

    /// Returns whether this error message is an expected-found message that
    /// [Error::merge_expected_found()] can be applied to.
    fn is_expected_found(&self) -> bool;

    /// Returns the location information associated with this error, if any.
    fn location(&self) -> At<&L::Location, &L::Span>;

    /// Constructor for a custom message with a location.
    fn custom<M: ToString>(msg: M, at: At<L::Location, L::Span>) -> Self;
}

/// Trait that allows fallback error messages to be constructed when no
/// generics are available.
pub trait Fallback {
    /// Constructor for a custom message without location data.
    fn fallback<M: ToString>(msg: M) -> Self;
}

/// Simple error message type.
pub enum Simple<'i, I, L>
where
    L: location::LocationTracker<I>,
{
    /// One of .0 was expected, but .1 was found at .2
    ExpectedFound(
        HashSet<Option<&'i I>>,
        Option<&'i I>,
        At<L::Location, L::Span>,
    ),

    /// Custom error message.
    Custom(String, At<L::Location, L::Span>),
}

impl<'i, I, L> Error<'i, I, L> for Simple<'i, I, L>
where
    I: 'i + Eq + std::hash::Hash,
    L: location::LocationTracker<I>,
{
    fn expected_found<J>(expected: J, found: Option<&'i I>, at: At<L::Location, L::Span>) -> Self
    where
        J: IntoIterator<Item = Option<&'i I>>,
        J::IntoIter: 'i,
    {
        Self::ExpectedFound(expected.into_iter().collect(), found, at)
    }

    fn merge_expected_found(&mut self, other: &Self) {
        if let (Self::ExpectedFound(dest, _, _), Self::ExpectedFound(src, _, _)) = (self, other) {
            dest.extend(src)
        }
    }

    fn is_expected_found(&self) -> bool {
        matches!(self, Self::ExpectedFound(_, _, _))
    }

    fn location(&self) -> At<&L::Location, &L::Span> {
        match self {
            Simple::ExpectedFound(_, _, l) => l.as_ref(),
            Simple::Custom(_, l) => l.as_ref(),
        }
    }

    fn custom<M: ToString>(msg: M, at: At<L::Location, L::Span>) -> Self {
        Self::Custom(msg.to_string(), at)
    }
}

impl<'i, I, L> Fallback for Simple<'i, I, L>
where
    L: location::LocationTracker<I>,
{
    fn fallback<M: ToString>(msg: M) -> Self {
        Self::Custom(msg.to_string(), At::None)
    }
}

impl<'i, I, L> std::fmt::Display for Simple<'i, I, L>
where
    L: location::LocationTracker<I>,
    &'i I: std::fmt::Display,
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
            Simple::Custom(msg, at) => {
                write!(f, "{msg}{at}")
            }
        }
    }
}
