// SPDX-License-Identifier: Apache-2.0

use std::borrow::Borrow;

use super::error;
use super::parser;
use super::stream;

/// See [empty()].
pub struct Empty<E> {
    phantom: std::marker::PhantomData<E>,
}

impl<E> Clone for Empty<E> {
    fn clone(&self) -> Self {
        Self {
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, E> parser::Parser<'i, H, I> for Empty<E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = ();
    type Error = E;

    fn parse_internal(
        &self,
        _stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        parser::Result::Success(())
    }
}

/// Match nothing; always succeeds. Returns ().
pub fn empty<E>() -> Empty<E> {
    Empty {
        phantom: Default::default(),
    }
}

/// See [none()].
pub struct None<O, E> {
    phantom: std::marker::PhantomData<(O, E)>,
}

impl<O, E> Clone for None<O, E> {
    fn clone(&self) -> Self {
        Self {
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, O, E> parser::Parser<'i, H, I> for None<O, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = Option<O>;
    type Error = E;

    fn parse_internal(
        &self,
        _stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        parser::Result::Success(None)
    }
}

/// Match nothing; always succeeds. Returns Option::None for the given option
/// type.
pub fn none<O, E>() -> None<O, E> {
    None {
        phantom: Default::default(),
    }
}

/// See [end()].
pub struct End<E> {
    phantom: std::marker::PhantomData<E>,
}

impl<E> Clone for End<E> {
    fn clone(&self) -> Self {
        Self {
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, E> parser::Parser<'i, H, I> for End<E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = ();
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        if stream.eof() {
            parser::Result::Success(())
        } else {
            parser::Result::Failed(
                stream.index(),
                vec![E::expected_found(
                    [None],
                    stream.token(),
                    error::At::Location(stream.location()),
                )],
            )
        }
    }
}

/// Match only end of file. Returns ().
pub fn end<E>() -> End<E> {
    End {
        phantom: Default::default(),
    }
}

/// See [just()].
pub struct Just<'i, H, I, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
{
    expected: H,
    phantom: std::marker::PhantomData<(&'i I, E)>,
}

impl<'i, H, I, E> Clone for Just<'i, H, I, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
{
    fn clone(&self) -> Self {
        Self {
            expected: self.expected.clone(),
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, E> parser::Parser<'i, H, I> for Just<'i, H, I, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = H;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Match the incoming token.
        let found = stream.token();
        if let Some(found) = &found {
            if found.borrow() == self.expected.borrow() {
                // Matched successfully, skip past it and return success.
                stream.advance();
                return parser::Result::Success(self.expected.clone());
            }
        }

        // Construct error message.
        parser::Result::Failed(
            stream.index(),
            vec![E::expected_found(
                [Some(self.expected.clone())],
                found,
                error::At::Span(stream.span()),
            )],
        )
    }
}

/// Match the given token exactly, returning a reference to the incoming token.
pub fn just<'i, H, I, E>(expected: H) -> Just<'i, H, I, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
{
    Just {
        expected,
        phantom: Default::default(),
    }
}

/// See [filter()].
pub struct Filter<F, E> {
    filter: F,
    phantom: std::marker::PhantomData<E>,
}

impl<F: Clone, E> Clone for Filter<F, E> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, F, E> parser::Parser<'i, H, I> for Filter<F, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + 'i,
    F: Fn(&I) -> bool,
    E: error::Error<'i, H, I>,
{
    type Output = H;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        stream.attempt(|stream| {
            // Match the incoming token.
            let found = stream.token();
            if let Some(found) = &found {
                if (self.filter)(found.borrow()) {
                    // Matched successfully, skip past it and return success.
                    stream.advance();
                    return Ok(parser::Result::Success(found.clone()));
                }
            }

            // Construct error message.
            Err(parser::Result::Failed(
                stream.index(),
                vec![E::expected_found([], found, error::At::Span(stream.span()))],
            ))
        })
    }
}

/// Match the incoming token with the given filter function, returning a
/// reference to the incoming token if the filter returned true.
pub fn filter<I, F, E>(filter: F) -> Filter<F, E>
where
    I: ?Sized,
    F: Fn(&I) -> bool,
{
    Filter {
        filter,
        phantom: Default::default(),
    }
}

/// See [filter_map()].
pub struct FilterMap<F, E> {
    filter: F,
    phantom: std::marker::PhantomData<E>,
}

impl<F: Clone, E> Clone for FilterMap<F, E> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, F, O, E> parser::Parser<'i, H, I> for FilterMap<F, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + 'i,
    F: Fn(&I) -> Option<O>,
    E: error::Error<'i, H, I>,
{
    type Output = O;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Match the incoming token.
        let found = stream.token();
        if let Some(found) = &found {
            if let Some(output) = (self.filter)(found.borrow()) {
                // Matched successfully, skip past it and return success.
                stream.advance();
                return parser::Result::Success(output);
            }
        }

        // Construct error message.
        parser::Result::Failed(
            stream.index(),
            vec![E::expected_found([], found, error::At::Span(stream.span()))],
        )
    }
}

/// Match the incoming token with the given filter function, returning the
/// result of the filter function if it returned Some.
pub fn filter_map<I, F, O, E>(filter: F) -> FilterMap<F, E>
where
    I: ?Sized,
    F: Fn(&I) -> Option<O>,
{
    FilterMap {
        filter,
        phantom: Default::default(),
    }
}

/// See [seq()].
pub struct Seq<'i, O, E> {
    expected: &'i O,
    phantom: std::marker::PhantomData<E>,
}

impl<'i, O, E> Clone for Seq<'i, O, E> {
    fn clone(&self) -> Self {
        Self {
            expected: self.expected,
            phantom: Default::default(),
        }
    }
}

impl<'i, H, I, O, E> parser::Parser<'i, H, I> for Seq<'i, O, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
    &'i O: IntoIterator<Item = H>,
    E: error::Error<'i, H, I>,
{
    type Output = &'i O;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        stream.attempt(|stream| {
            // Match concatenation of tokens returned by expected.
            for expected in self.expected.into_iter() {
                let found = stream.token();
                if let Some(found) = &found {
                    if found.borrow() == expected.borrow() {
                        stream.advance();
                        continue;
                    }
                }

                // Construct error message.
                return Err(parser::Result::Failed(
                    stream.index(),
                    vec![E::expected_found(
                        [Some(expected)],
                        found,
                        error::At::Span(stream.span()),
                    )],
                ));
            }

            // All elements were matched successfully.
            Ok(parser::Result::Success(self.expected))
        })
    }
}

/// Match the given sequence of tokens exactly, returning a reference to the
/// sequence.
///
/// Note: couldn't be bothered with the magic to make just() generic enough to
/// work for single inputs as well. I'm not sure how it works in Chumsky
/// exactly, but can't think of any reason why it wouldn't work here, too.
pub fn seq<'i, H, I, O, E>(expected: &'i O) -> Seq<'i, O, E>
where
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
    &'i O: IntoIterator<Item = H>,
{
    Seq {
        expected,
        phantom: Default::default(),
    }
}

/// See [one_of()].
pub struct OneOf<'i, G, E> {
    expected: &'i G,
    phantom: std::marker::PhantomData<E>,
}

impl<'i, G, E> Clone for OneOf<'i, G, E> {
    fn clone(&self) -> Self {
        Self {
            expected: self.expected,
            phantom: Default::default(),
        }
    }
}

impl<'i, G, H, I, E> parser::Parser<'i, H, I> for OneOf<'i, G, E>
where
    &'i G: IntoIterator<Item = H> + 'i,
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = H;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Get the next token from the input stream, and match it against the
        // set of alternatives.
        let found = stream.token();
        if let Some(found) = &found {
            for expected in self.expected.into_iter() {
                if found.borrow() == expected.borrow() {
                    stream.advance();
                    return parser::Result::Success(found.clone());
                }
            }
        }

        // Construct error message.
        parser::Result::Failed(
            stream.index(),
            vec![E::expected_found(
                self.expected.into_iter().map(Some),
                found,
                error::At::Span(stream.span()),
            )],
        )
    }
}

/// Match one of the given sequence of tokens exactly, returning a reference to
/// the incoming token that matched.
pub fn one_of<'i, G, H, I, E>(expected: &'i G) -> OneOf<G, E>
where
    &'i G: IntoIterator<Item = H> + 'i,
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
{
    OneOf {
        expected,
        phantom: Default::default(),
    }
}

/// See [none_of()].
pub struct NoneOf<'i, G, E> {
    rejected: &'i G,
    phantom: std::marker::PhantomData<E>,
}

impl<'i, G, E> Clone for NoneOf<'i, G, E> {
    fn clone(&self) -> Self {
        Self {
            rejected: self.rejected,
            phantom: Default::default(),
        }
    }
}

impl<'i, G, H, I, E> parser::Parser<'i, H, I> for NoneOf<'i, G, E>
where
    &'i G: IntoIterator<Item = H> + 'i,
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
    E: error::Error<'i, H, I>,
{
    type Output = H;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, H, I, E::LocationTracker>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Get the next token from the input stream, and match it against the
        // set of alternatives.
        let found = stream.token();
        if let Some(found) = found {
            for expected in self.rejected.into_iter() {
                if found.borrow() == expected.borrow() {
                    // Construct error message.
                    return parser::Result::Failed(
                        stream.index(),
                        vec![E::expected_found(
                            [],
                            Some(found),
                            error::At::Span(stream.span()),
                        )],
                    );
                }
            }

            // Found a token that isn't rejected.
            stream.advance();
            parser::Result::Success(found)
        } else {
            // Found EOF.
            parser::Result::Failed(
                stream.index(),
                vec![E::expected_found(
                    [],
                    None,
                    error::At::Location(stream.location()),
                )],
            )
        }
    }
}

/// Match the next token if it matches none of the given tokens, returning a
/// reference to the incoming token that matched.
pub fn none_of<'i, G, H, I, E>(rejected: &'i G) -> NoneOf<'i, G, E>
where
    &'i G: IntoIterator<Item = H> + 'i,
    H: Borrow<I> + Clone + 'i,
    I: ?Sized + PartialEq + 'i,
{
    NoneOf {
        rejected,
        phantom: Default::default(),
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn test_empty() {
        let parser = empty::<SimpleError<_, char>>().clone();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(())));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['a', 'b', 'c']
        );
    }

    #[test]
    fn test_none() {
        let parser = none::<usize, SimpleError<_, char>>().clone();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(None)));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['a', 'b', 'c']
        );
    }

    #[test]
    fn test_end() {
        let parser = end::<SimpleError<_, char>>().clone();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['a', 'b', 'c']
        );
        assert_eq!(parser.parse(&[]), Ok(()));
    }

    #[test]
    fn test_just() {
        let parser = just(&'a').with_error::<SimpleError<_, char>>().clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Success(&'a'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );
    }

    #[test]
    fn test_filter() {
        let parser = filter(|x| *x == 'a')
            .with_error::<SimpleError<_, char>>()
            .clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Success(&'a'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );
    }

    #[test]
    fn test_filter_map() {
        let parser = filter_map(|x| if *x == 'a' { Some('A') } else { None })
            .with_error::<SimpleError<_, char>>()
            .clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Success('A'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );
    }

    #[test]
    fn test_seq() {
        let parser = seq::<_, &char, _, _>(&['a', 'b'])
            .with_error::<SimpleError<_, char>>()
            .clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(
            stream.next(),
            Some(ParseResult::Success(&['a', 'b']))
        ));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );

        let mut stream = parser.stream(&['a', 'c', 'b']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(1, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['a', 'c', 'b']
        );
    }

    #[test]
    fn test_one_of() {
        let parser = one_of::<_, _, &char, _>(&['a', 'b'])
            .with_error::<SimpleError<_, char>>()
            .clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Success(&'a'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Success(&'b'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'a']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );
    }

    #[test]
    fn test_none_of() {
        let parser = none_of::<_, _, &char, _>(&['a', 'b'])
            .with_error::<SimpleError<_, char>>()
            .clone();

        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['a', 'b', 'c']
        );

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['b', 'c', 'a']
        );

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Success(&'c'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'a']);
    }
}
