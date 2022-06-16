// SPDX-License-Identifier: Apache-2.0

use super::algorithm;
use super::error;
use super::location;
use super::parser;
use super::primitive;
use super::recovery;
use super::stream;
use std::rc::Rc;

/// See [parser::Parser::boxed()].
pub struct Boxed<'i, I, O, E = error::Simple<'i, I>> {
    pub(crate) child: Rc<dyn parser::Parser<'i, Input = I, Output = O, Error = E> + 'i>,
}

impl<'i, I, O, E> Clone for Boxed<'i, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            child: self.child.clone(),
        }
    }
}

impl<'i, I, O, E> parser::Parser<'i> for Boxed<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    type Input = I;
    type Output = O;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.child.parse_internal(stream, enable_recovery)
    }
}

/// See [parser::Parser::with_error()].
pub struct WithError<C, E> {
    pub(crate) child: C,
    pub(crate) phantom: std::marker::PhantomData<E>,
}

impl<'i, C> parser::Parser<'i> for WithError<C, C::Error>
where
    C: parser::Parser<'i>,
{
    type Input = C::Input;
    type Output = C::Output;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_internal(stream, enable_recovery)
    }
}

/// See [parser::Parser::to()].
pub struct To<C, O> {
    pub(crate) child: C,
    pub(crate) to: O,
}

impl<'i, C, O> parser::Parser<'i> for To<C, O>
where
    C: parser::Parser<'i>,
    O: Clone,
{
    type Input = C::Input;
    type Output = O;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child
            .parse_internal(stream, enable_recovery)
            .map(|_| self.to.clone())
    }
}

/// See [parser::Parser::ignored()].
pub type Ignored<C> = To<C, ()>;

/// See [parser::Parser::some()].
pub struct Some<C> {
    pub(crate) child: C,
}

impl<'i, C> parser::Parser<'i> for Some<C>
where
    C: parser::Parser<'i>,
{
    type Input = C::Input;
    type Output = Option<C::Output>;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_internal(stream, enable_recovery).map(Some)
    }
}

/// See [parser::Parser::map()].
pub struct Map<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, C, F, O> parser::Parser<'i> for Map<C, F>
where
    C: parser::Parser<'i>,
    F: Fn(C::Output) -> O,
{
    type Input = C::Input;
    type Output = O;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child
            .parse_internal(stream, enable_recovery)
            .map(&self.map)
    }
}

/// See [parser::Parser::map_with_span()].
pub struct MapWithSpan<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, C, F, O> parser::Parser<'i> for MapWithSpan<C, F>
where
    C: parser::Parser<'i>,
    F: Fn(
        C::Output,
        <<C::Error as error::Error<'i, C::Input>>::LocationTracker as location::Tracker<C::Input>>::Span,
    ) -> O,
{
    type Input = C::Input;
    type Output = O;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        let from = stream.save();
        self.child
            .parse_internal(stream, enable_recovery)
            .map(|a| (self.map)(a, stream.spanning_back_to(&from)))
    }
}

/// See [parser::Parser::map_err()].
pub struct MapErr<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, C, F, E> parser::Parser<'i> for MapErr<C, F>
where
    C: parser::Parser<'i>,
    F: Fn(C::Error) -> E,
    E: error::Error<'i, C::Input, LocationTracker = <C::Error as error::Error<'i, C::Input>>::LocationTracker>,
{
    type Input = C::Input;
    type Output = C::Output;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child
            .parse_internal(stream, enable_recovery)
            .map_err(&self.map)
    }
}

/// See [parser::Parser::map_err_with_span()].
pub struct MapErrWithSpan<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, C, F, E> parser::Parser<'i> for MapErrWithSpan<C, F>
where
    C: parser::Parser<'i>,
    F: Fn(
        C::Error,
        <<C::Error as error::Error<'i, C::Input>>::LocationTracker as location::Tracker<C::Input>>::Span,
    ) -> E,
    E: error::Error<'i, C::Input, LocationTracker = <C::Error as error::Error<'i, C::Input>>::LocationTracker>,
{
    type Input = C::Input;
    type Output = C::Output;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        let from = stream.save();
        self.child
            .parse_internal(stream, enable_recovery)
            .map_err(|e| (self.map)(e, stream.spanning_back_to(&from)))
    }
}

/// Special result type to be returned by the function passed to
/// [parser::Parser::try_map()], which, in addition to Ok and Err,
/// has a variant for recoverable errors.
pub enum TryMapResult<O, E> {
    Ok(O),
    Err(Vec<E>),
    Recovered(O, Vec<E>),
}

/// See [parser::Parser::try_map()].
pub struct TryMap<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, C, F, O> parser::Parser<'i> for TryMap<C, F>
where
    C: parser::Parser<'i>,
    F: Fn(
        C::Output,
        <<C::Error as error::Error<'i, C::Input>>::LocationTracker as location::Tracker<C::Input>>::Span,
    ) -> TryMapResult<O, C::Error>,
{
    type Input = C::Input;
    type Output = O;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        let initial = stream.save();
        self.child
            .parse_internal(stream, enable_recovery)
            .try_map(|a| match (self.map)(a, stream.spanning_back_to(&initial)) {
                TryMapResult::Ok(o) => parser::Result::Success(o),
                TryMapResult::Err(es) => {
                    assert!(!es.is_empty());
                    stream.restore(&initial);
                    parser::Result::Failed(stream.index_at(&initial), es)
                }
                TryMapResult::Recovered(o, es) => {
                    assert!(!es.is_empty());
                    if enable_recovery {
                        parser::Result::Recovered(o, es)
                    } else {
                        parser::Result::Failed(stream.index_at(&initial), es)
                    }
                }
            })
    }
}

/// See [parser::Parser::then()].
pub struct Then<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, A, B> parser::Parser<'i> for Then<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = (A::Output, B::Output);
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        concatenate!(stream, enable_recovery, |x| x, self.a, self.b)
    }
}

/// See [parser::Parser::then_ignore()].
pub struct ThenIgnore<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, A, B> parser::Parser<'i> for ThenIgnore<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = A::Output;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        concatenate!(stream, enable_recovery, |(a, _b)| a, self.a, self.b)
    }
}

/// See [parser::Parser::ignore_then()].
pub struct IgnoreThen<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, A, B> parser::Parser<'i> for IgnoreThen<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = B::Output;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        concatenate!(stream, enable_recovery, |(_a, b)| b, self.a, self.b)
    }
}

/// See [parser::Parser::delimited_by()].
pub struct DelimitedBy<A, B, C> {
    pub(crate) left: A,
    pub(crate) middle: B,
    pub(crate) right: C,
}

impl<'i, A, B, C> parser::Parser<'i> for DelimitedBy<A, B, C>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
    C: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = B::Output;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        concatenate!(
            stream,
            enable_recovery,
            |(_l, m, _r)| m,
            self.left,
            self.middle,
            self.right
        )
    }
}

/// See [parser::Parser::padded_by()].
pub struct PaddedBy<A, B> {
    pub(crate) padding: A,
    pub(crate) middle: B,
}

impl<'i, A, B> parser::Parser<'i> for PaddedBy<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = B::Output;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        concatenate!(
            stream,
            enable_recovery,
            |(_l, m, _r)| m,
            self.padding,
            self.middle,
            self.padding
        )
    }
}

/// See [parser::Parser::chain()].
pub struct Chain<'i, I, O, E> {
    pub(crate) parsers: Vec<Boxed<'i, I, O, E>>,
}

impl<'i, I, O, E> parser::Parser<'i> for Chain<'i, I, O, E>
where
    I: 'i,
    O: 'i,
    E: error::Error<'i, I>,
{
    type Input = I;
    type Output = Vec<O>;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        algorithm::concatenate(stream, enable_recovery, &self.parsers)
    }
}

impl<'i, I, O, E> Chain<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    /// Append an additional parser to this chain.
    pub fn and<B>(self, other: B) -> Chain<'i, I, O, E>
    where
        B: parser::Parser<'i, Input = I, Output = O, Error = E> + 'i,
    {
        let mut parsers = self.parsers;
        parsers.push(other.boxed());
        Chain { parsers }
    }
}

/// See [parser::Parser::or()].
pub struct Or<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, A, B> parser::Parser<'i> for Or<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Output = A::Output, Error = A::Error>,
{
    type Input = A::Input;
    type Output = A::Output;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<A::Output, Self::Error> {
        alternate!(stream, enable_recovery, &self.a, &self.b)
    }
}

/// See [parser::Parser::or_not()].
pub struct OrNot<C> {
    pub(crate) child: Some<C>,
}

impl<'i, C> parser::Parser<'i> for OrNot<C>
where
    C: parser::Parser<'i>,
{
    type Input = C::Input;
    type Output = Option<C::Output>;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        alternate!(
            stream,
            enable_recovery,
            &self.child,
            &primitive::none::<C::Output, C::Error>()
        )
    }
}

/// See [parser::Parser::alters()].
pub struct Alters<'i, I, O, E> {
    pub(crate) parsers: Vec<Boxed<'i, I, O, E>>,
}

impl<'i, I, O, E> parser::Parser<'i> for Alters<'i, I, O, E>
where
    I: 'i,
    O: 'i,
    E: error::Error<'i, I>,
{
    type Input = I;
    type Output = O;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        algorithm::alternate(stream, enable_recovery, &self.parsers)
    }
}

impl<'i, I, O, E> Alters<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    /// Append an additional parser to this chain.
    pub fn and<B>(self, other: B) -> Alters<'i, I, O, E>
    where
        B: parser::Parser<'i, Input = I, Output = O, Error = E> + 'i,
    {
        let mut parsers = self.parsers;
        parsers.push(other.boxed());
        Alters { parsers }
    }
}

/// See [parser::Parser::separated_by()].
pub struct SeparatedBy<A, B> {
    pub(crate) minimum: usize,
    pub(crate) maximum: Option<usize>,
    pub(crate) item: A,
    pub(crate) separator: Option<B>,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
}

impl<'i, A, B> parser::Parser<'i> for SeparatedBy<A, B>
where
    A: parser::Parser<'i>,
    B: parser::Parser<'i, Input = A::Input, Error = A::Error>,
{
    type Input = A::Input;
    type Output = Vec<A::Output>;
    type Error = A::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        algorithm::repeat(
            stream,
            enable_recovery,
            self.minimum,
            self.maximum,
            &self.item,
            self.separator.as_ref(),
            self.allow_leading,
            self.allow_trailing,
        )
    }
}

impl<A, B> SeparatedBy<A, B> {
    /// Require at least the given amount of iterations.
    pub fn at_least(mut self, minimum: usize) -> Self {
        self.minimum = minimum;
        self
    }

    /// Require at most the given amount of iterations.
    pub fn at_most(mut self, maximum: usize) -> Self {
        self.maximum = Some(maximum);
        self
    }

    /// Require exactly given amount of iterations.
    pub fn exactly(mut self, amount: usize) -> Self {
        self.minimum = amount;
        self.maximum = Some(amount);
        self
    }

    /// Require separators to exist between the repetitions. The result of the
    /// separator parser is ignored.
    pub fn with_separator(mut self, separator: B) -> Self {
        self.separator = Some(separator);
        self
    }

    /// Allow a leading separator to appear before the first item. This is
    /// allowed even if no items are parsed.
    pub fn allow_leading(mut self) -> Self {
        self.allow_leading = true;
        self
    }

    /// Allow a trailing separator to appear after the last item. This is
    /// allowed only if at least one item is parsed.
    pub fn allow_trailing(mut self) -> Self {
        self.allow_trailing = true;
        self
    }
}

/// See [parser::Parser::repeated()].
pub type Repeated<A> = SeparatedBy<A, A>;

/// See [parser::Parser::to_recover()].
pub struct ToRecover<C, S> {
    pub(crate) parser: C,
    pub(crate) strategy: S,
}

impl<'i, C, S> parser::Parser<'i> for ToRecover<C, S>
where
    C: parser::Parser<'i>,
    S: recovery::Strategy<'i, C>,
{
    type Input = C::Input;
    type Output = C::Output;
    type Error = C::Error;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, Self::Input, <Self::Error as error::Error<'i, Self::Input>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        match self.parser.parse_internal(stream, enable_recovery) {
            parser::Result::Failed(last_token_matched, mut errors) => {
                if !enable_recovery {
                    // Recovery disabled, don't run recovery strategy.
                    parser::Result::Failed(last_token_matched, errors)
                } else {
                    let started_at = stream.save();
                    let mut failed_at = stream.save_at(last_token_matched);
                    let recovery = recovery::Strategy::recover(
                        &self.strategy,
                        &self.parser,
                        stream,
                        &started_at,
                        &mut failed_at,
                        &mut errors,
                    );
                    if let Some(output) = recovery {
                        // Recovery successful.
                        parser::Result::Recovered(output, errors)
                    } else {
                        // Recovery failed, but note that `errors` may have been
                        // modified by the recovery strategy.
                        parser::Result::Failed(last_token_matched, errors)
                    }
                }
            }
            // Don't run recovery if the parser was successful (obviously) or
            // if a previous recovery strategy was already successful.
            r => r,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn test_boxed() {
        let parser = just(&'a').boxed().with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    #[test]
    fn test_to() {
        let parser = just(&'a').to(42usize).with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(42usize)));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    #[test]
    fn test_map() {
        let parser = just(&'a')
            .map(|x| x.to_ascii_uppercase())
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success('A')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    #[test]
    fn test_map_with_span() {
        let parser = just(&'a')
            .map_with_span(|x, s| (x.to_ascii_uppercase(), s))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(('A', 0..1))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    // TODO map_err, map_err_with_span, try_map

    #[test]
    fn test_then() {
        let parser = just(&'a')
            .then(just(&'b'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success((&'a', &'b'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'c', 'b']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(1, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'c', 'b']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_then_ignore() {
        let parser = just(&'a')
            .then_ignore(just(&'b'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'c', 'b']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(1, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'c', 'b']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_ignore_then() {
        let parser = just(&'a')
            .ignore_then(just(&'b'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'b')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'c', 'b']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(1, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'c', 'b']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_padded_by() {
        let parser = just(&'a')
            .padded_by(just(&'b'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['b', 'a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['b', 'a', 'c', 'b']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(2, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'a', 'c', 'b']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_delimited_by() {
        let parser = just(&'b')
            .delimited_by(just(&'a'), just(&'c'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c', 'd']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'b')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['d']);

        let mut stream = parser.stream(&['a', 'b', 'd', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(2, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'b', 'd', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_chain() {
        let parser = just(&'a')
            .chain(just(&'b'))
            .and(just(&'c'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c', 'd']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'b', &'c'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['d']);

        let mut stream = parser.stream(&['a', 'b', 'd', 'c']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(2, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'b', 'd', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_or() {
        let parser = just(&'a')
            .or(just(&'b'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'b')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'a']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'b', 'a']);
    }

    #[test]
    fn test_alters() {
        let parser = just(&'a')
            .alters(just(&'b'))
            .and(just(&'c'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'b')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c', 'a']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'c')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'a']);

        let mut stream = parser.stream(&['d', 'b', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['d', 'b', 'a']);
    }

    #[test]
    fn test_or_not() {
        let parser = just(&'a')
            .or_not()
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(Some(&'a'))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(None)));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);
    }

    #[test]
    fn test_repeated_any() {
        let parser = just(&'a')
            .repeated()
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['a', 'a', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![]);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);
    }

    #[test]
    fn test_repeated_many() {
        let parser = just(&'a')
            .repeated()
            .at_least(1)
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['a', 'a', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![]);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert!(matches!(stream.next(), Some(ParseResult::Failed(0, _))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);
    }

    #[test]
    fn test_repeated_max() {
        let parser = just(&'a')
            .repeated()
            .at_most(2)
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['a', 'a', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);
    }

    #[test]
    fn test_separated_by() {
        let parser = just(&'a')
            .separated_by(just(&','))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', ',', 'b', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'b', ',', 'c']);

        let mut stream = parser.stream(&['a', ',', 'a', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'a']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);

        let mut stream = parser.stream(&[',', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'a']);

        let mut stream = parser.stream(&['a', ',']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',']);
    }

    #[test]
    fn test_separated_by_allow_leading() {
        let parser = just(&'a')
            .separated_by(just(&','))
            .allow_leading()
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', ',', 'b', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'b', ',', 'c']);

        let mut stream = parser.stream(&['a', ',', 'a', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'a']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);

        let mut stream = parser.stream(&[',', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![]);

        let mut stream = parser.stream(&['a', ',']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',']);
    }

    #[test]
    fn test_separated_by_allow_trailing() {
        let parser = just(&'a')
            .separated_by(just(&','))
            .allow_trailing()
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', ',', 'b', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', ',', 'c']);

        let mut stream = parser.stream(&['a', ',', 'a', ',', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a', &'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['c']);

        let mut stream = parser.stream(&['a', 'a', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['a', 'a']);

        let mut stream = parser.stream(&['b', 'c', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c', 'a']);

        let mut stream = parser.stream(&[',', 'a']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![',', 'a']);

        let mut stream = parser.stream(&['a', ',']);
        assert_eq!(stream.next(), Some(ParseResult::Success(vec![&'a'])));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec![]);
    }

}
