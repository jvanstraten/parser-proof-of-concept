use std::collections::HashSet;

use super::location;

/// Trait that allows error messages to be constructed.
pub trait Error<'i, I, L>
where
    I: 'i,
    L: location::LocationTracker<I>,
{
    /// Constructor for error messages stating that one of a number of tokens
    /// was expected but another was found. The span corresponds to the token
    /// that was found. None is used for EOF.
    fn expected_found<J>(expected: J, found: Option<&'i I>, at: L::Span) -> Self
    where
        J: IntoIterator<Item = Option<&'i I>>,
        J::IntoIter: 'i;

    /// Adds to the set of expected tokens by means of the given other
    /// expected-found message.
    fn merge_expected_found(&mut self, other: &Self);

    fn internal_error() -> Self;
}

/// Simple error message type.
pub enum Simple<'i, I, L>
where
    I: 'i + std::fmt::Display + Eq + std::hash::Hash,
    L: location::LocationTracker<I>,
    L::Span: std::fmt::Display,
{
    /// One of .0 was expected, but .1 was found at .2
    ExpectedFound(HashSet<Option<&'i I>>, Option<&'i I>, L::Span),

    /// Custom error message.
    Custom(String),
}

impl<'i, I, L> Error<'i, I, L> for Simple<'i, I, L>
where
    I: 'i + std::fmt::Display + Eq + std::hash::Hash,
    L: location::LocationTracker<I>,
    L::Span: std::fmt::Display,
{
    fn expected_found<J>(expected: J, found: Option<&'i I>, at: L::Span) -> Self
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

    fn internal_error() -> Self {
        Self::Custom(String::from("internal error"))
    }
}

impl<'i, I, L> Simple<'i, I, L>
where
    I: 'i + std::fmt::Display + Eq + std::hash::Hash,
    L: location::LocationTracker<I>,
    L::Span: std::fmt::Display,
{
    /// Constructs a custom error message.
    pub fn custom<S: ToString>(message: S) -> Self {
        Self::Custom(message.to_string())
    }
}
