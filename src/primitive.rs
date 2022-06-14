// SPDX-License-Identifier: Apache-2.0

use super::error;
use super::location;
use super::parser;

/// See [empty()].
pub struct Empty();

impl<'i, I, L, E> parser::Parser<'i, I, L, E> for Empty
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = ();

    fn parse_internal(
        &self,
        _stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        parser::Result::Success(())
    }
}

/// Match nothing; always succeeds. Returns ().
pub fn empty() -> Empty {
    Empty()
}

/// See [none()].
pub struct None<O> {
    phantom: std::marker::PhantomData<O>,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for None<O>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = Option<O>;

    fn parse_internal(
        &self,
        _stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        parser::Result::Success(None)
    }
}

/// Match nothing; always succeeds. Returns Option::None for the given option
/// type.
pub fn none<O>() -> None<O> {
    None {
        phantom: Default::default(),
    }
}

/// See [end()].
pub struct End();

impl<'i, I, L, E> parser::Parser<'i, I, L, E> for End
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = ();

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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
pub fn end() -> End {
    End()
}

/// See [just()].
pub struct Just<'i, I>
where
    I: 'i + PartialEq,
{
    expected: &'i I,
}

impl<'i, I, L, E> parser::Parser<'i, I, L, E> for Just<'i, I>
where
    I: 'i + PartialEq,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i I;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Save the initial parser state, so we can restore it if we encounter
        // an error.
        let initial = stream.save();

        // Match the incoming token.
        let found = stream.token();
        if found == Some(self.expected) {
            // Matched successfully, skip past it and return success.
            stream.advance();
            parser::Result::Success(self.expected)
        } else {
            // Get error information from the stream, then restore it to
            // the initial position.
            let successful_up_to = stream.index();
            let from = stream.save();
            stream.advance();
            let span = stream.spanning_back_to(&from);
            drop(from);
            stream.restore(&initial);
            drop(initial);

            // Construct error message.
            parser::Result::Failed(
                successful_up_to,
                vec![E::expected_found(
                    [Some(self.expected)],
                    found,
                    error::At::Span(span),
                )],
            )
        }
    }
}

/// Match the given token exactly, returning a reference to the incoming token.
pub fn just<'i, I>(expected: &'i I) -> Just<'i, I>
where
    I: 'i + PartialEq,
{
    Just { expected }
}

/// See [filter()].
pub struct Filter<I, F>
where
    F: Fn(&I) -> bool,
{
    filter: F,
    phantom: std::marker::PhantomData<I>,
}

impl<'i, I, F, L, E> parser::Parser<'i, I, L, E> for Filter<I, F>
where
    I: 'i,
    F: Fn(&I) -> bool,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i I;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Save the initial parser state, so we can restore it if we encounter
        // an error.
        let initial = stream.save();

        // Match the incoming token.
        let found = stream.token();
        if let Some(found) = found {
            if (self.filter)(found) {
                // Matched successfully, skip past it and return success.
                stream.advance();
                return parser::Result::Success(found);
            }
        }

        // Get error information from the stream, then restore it to
        // the initial position.
        let successful_up_to = stream.index();
        let from = stream.save();
        stream.advance();
        let span = stream.spanning_back_to(&from);
        drop(from);
        stream.restore(&initial);
        drop(initial);

        // Construct error message.
        parser::Result::Failed(
            successful_up_to,
            vec![E::expected_found([], found, error::At::Span(span))],
        )
    }
}

/// Match the incoming token with the given filter function, returning a
/// reference to the incoming token if the filter returned true.
pub fn filter<I, F>(filter: F) -> Filter<I, F>
where
    F: Fn(&I) -> bool,
{
    Filter {
        filter,
        phantom: Default::default(),
    }
}

/// See [filter_map()].
pub struct FilterMap<I, O, F>
where
    F: Fn(&I) -> Option<O>,
{
    filter: F,
    phantom: std::marker::PhantomData<(I, O)>,
}

impl<'i, I, O, F, L, E> parser::Parser<'i, I, L, E> for FilterMap<I, O, F>
where
    I: 'i,
    F: Fn(&I) -> Option<O>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Save the initial parser state, so we can restore it if we encounter
        // an error.
        let initial = stream.save();

        // Match the incoming token.
        let found = stream.token();
        if let Some(found) = found {
            if let Some(output) = (self.filter)(found) {
                // Matched successfully, skip past it and return success.
                stream.advance();
                return parser::Result::Success(output);
            }
        }

        // Get error information from the stream, then restore it to
        // the initial position.
        let successful_up_to = stream.index();
        let from = stream.save();
        stream.advance();
        let span = stream.spanning_back_to(&from);
        drop(from);
        stream.restore(&initial);
        drop(initial);

        // Construct error message.
        parser::Result::Failed(
            successful_up_to,
            vec![E::expected_found([], found, error::At::Span(span))],
        )
    }
}

/// Match the incoming token with the given filter function, returning the
/// result of the filter function if it returned Some.
pub fn filter_map<I, O, F>(filter: F) -> FilterMap<I, O, F>
where
    F: Fn(&I) -> Option<O>,
{
    FilterMap {
        filter,
        phantom: Default::default(),
    }
}

/// See [seq()].
pub struct Seq<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    expected: &'i O,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for Seq<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Save the initial parser state, so we can restore it if we encounter
        // an error.
        let initial = stream.save();

        // Match concatenation of tokens returned by expected.
        for expected in self.expected.into_iter() {
            let found = stream.token();
            if found == Some(expected) {
                stream.advance();
            } else {
                // Get error information from the stream, then restore it to
                // the initial position.
                let successful_up_to = stream.index();
                let from = stream.save();
                stream.advance();
                let span = stream.spanning_back_to(&from);
                drop(from);
                stream.restore(&initial);
                drop(initial);

                // Construct error message.
                return parser::Result::Failed(
                    successful_up_to,
                    vec![E::expected_found(
                        [Some(expected)],
                        found,
                        error::At::Span(span),
                    )],
                );
            }
        }

        // All elements were matched successfully.
        parser::Result::Success(self.expected)
    }
}

/// Match the given sequence of tokens exactly, returning a reference to the
/// sequence.
///
/// Note: couldn't be bothered with the magic to make just() generic enough to
/// work for single inputs as well. I'm not sure how it works in Chumsky
/// exactly, but can't think of any reason why it wouldn't work here, too.
pub fn seq<'i, I, O>(expected: &'i O) -> Seq<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    Seq { expected }
}

/// See [one_of()].
pub struct OneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    expected: &'i O,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for OneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i I;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Get the next token from the input stream, and match it against the
        // set of alternatives.
        let found = stream.token();
        if let Some(found) = found {
            for expected in self.expected.into_iter() {
                if found == expected {
                    stream.advance();
                    return parser::Result::Success(found);
                }
            }
        }

        // Get error information from the stream, then restore it to
        // the initial position.
        let successful_up_to = stream.index();
        let from = stream.save();
        stream.advance();
        let span = stream.spanning_back_to(&from);
        stream.restore(&from);
        drop(from);

        // Construct error message.
        parser::Result::Failed(
            successful_up_to,
            vec![E::expected_found(
                self.expected.into_iter().map(Some),
                found,
                error::At::Span(span),
            )],
        )
    }
}

/// Match one of the given sequence of tokens exactly, returning a reference to
/// the incoming token that matched.
pub fn one_of<'i, I, O>(expected: &'i O) -> OneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    OneOf { expected }
}

/// See [none_of()].
pub struct NoneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    rejected: &'i O,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for NoneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i I;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        _enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Get the next token from the input stream, and match it against the
        // set of alternatives.
        let found = stream.token();
        if let Some(found) = found {
            for expected in self.rejected.into_iter() {
                if found == expected {
                    // Get error information from the stream, then restore it to
                    // the initial position.
                    let successful_up_to = stream.index();
                    let from = stream.save();
                    stream.advance();
                    let span = stream.spanning_back_to(&from);
                    stream.restore(&from);
                    drop(from);

                    // Construct error message.
                    return parser::Result::Failed(
                        successful_up_to,
                        vec![E::expected_found([], Some(found), error::At::Span(span))],
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
pub fn none_of<'i, I, O>(rejected: &'i O) -> NoneOf<'i, I, O>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
{
    NoneOf { rejected }
}
