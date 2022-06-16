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
    pub(crate) parser: Rc<dyn parser::Parser<'i, I, E, Output = O> + 'i>,
}

impl<'i, I, O, E> Clone for Boxed<'i, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
        }
    }
}

impl<'i, I, O, E> parser::Parser<'i, I, E> for Boxed<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.parser.parse_internal(stream, enable_recovery)
    }
}

/// See [parser::Parser::to()].
pub struct To<C, O> {
    pub(crate) child: C,
    pub(crate) to: O,
}

impl<'i, I, C, O, E> parser::Parser<'i, I, E> for To<C, O>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    O: Clone,
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, C, E> parser::Parser<'i, I, E> for Some<C>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = Option<C::Output>;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.child.parse_internal(stream, enable_recovery).map(Some)
    }
}

/// See [parser::Parser::map()].
pub struct Map<C, F> {
    pub(crate) child: C,
    pub(crate) map: F,
}

impl<'i, I, C, F, O, E> parser::Parser<'i, I, E> for Map<C, F>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    F: Fn(C::Output) -> O,
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, C, F, O, E> parser::Parser<'i, I, E> for MapWithSpan<C, F>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    F: Fn(C::Output, <E::Location as location::LocationTracker<I>>::Span) -> O,
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        let from = stream.save();
        self.child
            .parse_internal(stream, enable_recovery)
            .map(|a| (self.map)(a, stream.spanning_back_to(&from)))
    }
}

/// See [parser::Parser::map_err()].
pub struct MapErr<C, F, A> {
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<A>,
}

impl<'i, I, C, A, F, E> parser::Parser<'i, I, E> for MapErr<C, F, A>
where
    I: 'i,
    C: parser::Parser<'i, I, A>,
    A: error::Error<'i, I>,
    F: Fn(A) -> E,
    E: error::Error<'i, I, Location = A::Location>,
{
    type Output = C::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, A::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.child
            .parse_internal(stream, enable_recovery)
            .map_err(&self.map)
    }
}

/// See [parser::Parser::map_err_with_span()].
pub struct MapErrWithSpan<C, F, A> {
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<A>,
}

impl<'i, I, C, A, F, E> parser::Parser<'i, I, E> for MapErrWithSpan<C, F, A>
where
    I: 'i,
    C: parser::Parser<'i, I, A>,
    A: error::Error<'i, I>,
    F: Fn(A, <A::Location as location::LocationTracker<I>>::Span) -> E,
    E: error::Error<'i, I, Location = A::Location>,
{
    type Output = C::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, A::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, C, F, O, E> parser::Parser<'i, I, E> for TryMap<C, F>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    F: Fn(C::Output, <E::Location as location::LocationTracker<I>>::Span) -> TryMapResult<O, E>, // TODO Into<TryMapResult<O, E>>, impl Result -> TryMapResult
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, A, B, E> parser::Parser<'i, I, E> for Then<A, B>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = (A::Output, B::Output);

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        concatenate!(stream, enable_recovery, |x| x, self.a, self.b)
    }
}

/// See [parser::Parser::then_ignore()].
pub struct ThenIgnore<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, I, A, B, E> parser::Parser<'i, I, E> for ThenIgnore<A, B>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = A::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        concatenate!(stream, enable_recovery, |(a, _b)| a, self.a, self.b)
    }
}

/// See [parser::Parser::ignore_then()].
pub struct IgnoreThen<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<'i, I, A, B, E> parser::Parser<'i, I, E> for IgnoreThen<A, B>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        concatenate!(stream, enable_recovery, |(_a, b)| b, self.a, self.b)
    }
}

/// See [parser::Parser::delimited_by()].
pub struct DelimitedBy<A, B, C> {
    pub(crate) left: A,
    pub(crate) middle: B,
    pub(crate) right: C,
}

impl<'i, I, A, B, C, E> parser::Parser<'i, I, E> for DelimitedBy<A, B, C>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E>,
    C: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, A, B, E> parser::Parser<'i, I, E> for PaddedBy<A, B>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<'i, I, O, E> parser::Parser<'i, I, E> for Chain<'i, I, O, E>
where
    I: 'i,
    O: 'i,
    E: error::Error<'i, I>,
{
    type Output = Vec<O>;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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
        B: parser::Parser<'i, I, E, Output = O> + 'i,
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

impl<'i, I, A, B, E> parser::Parser<'i, I, E> for Or<A, B>
where
    I: 'i,
    E: error::Error<'i, I>,
    A: parser::Parser<'i, I, E>,
    B: parser::Parser<'i, I, E, Output = A::Output>,
{
    type Output = A::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<A::Output, E> {
        alternate!(stream, enable_recovery, &self.a, &self.b)
    }
}

/// See [parser::Parser::or_not()].
pub struct OrNot<C> {
    pub(crate) child: Some<C>,
}

impl<'i, I, C, E> parser::Parser<'i, I, E> for OrNot<C>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = Option<C::Output>;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        alternate!(
            stream,
            enable_recovery,
            &self.child,
            &primitive::none::<C::Output>()
        )
    }
}

/// See [parser::Parser::chain_alternatives()].
pub struct ChainAlternatives<'i, I, O, E> {
    pub(crate) parsers: Vec<Boxed<'i, I, O, E>>,
}

impl<'i, I, O, E> parser::Parser<'i, I, E> for ChainAlternatives<'i, I, O, E>
where
    I: 'i,
    O: 'i,
    E: error::Error<'i, I>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        algorithm::alternate(stream, enable_recovery, &self.parsers)
    }
}

impl<'i, I, O, E> ChainAlternatives<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    /// Append an additional parser to this chain.
    pub fn and<B>(self, other: B) -> Chain<'i, I, O, E>
    where
        B: parser::Parser<'i, I, E, Output = O> + 'i,
    {
        let mut parsers = self.parsers;
        parsers.push(other.boxed());
        Chain { parsers }
    }
}

/// See [parser::Parser::repeated()].
pub struct Repeated<A, B = primitive::Empty> {
    pub(crate) minimum: usize,
    pub(crate) maximum: Option<usize>,
    pub(crate) item: A,
    pub(crate) separator: Option<B>,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
}

impl<'i, I, A, E> parser::Parser<'i, I, E> for Repeated<A>
where
    I: 'i,
    A: parser::Parser<'i, I, E>,
    E: error::Error<'i, I>,
{
    type Output = Vec<A::Output>;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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

impl<A, B> Repeated<A, B> {
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

/// See [parser::Parser::separated_by()].
pub type SeparatedBy<A, B> = Repeated<A, B>;

/// See [parser::Parser::recover_with()].
pub struct RecoverWith<C, S> {
    pub(crate) parser: C,
    pub(crate) strategy: S,
}

impl<'i, I, C, S, E> parser::Parser<'i, I, E> for RecoverWith<C, S>
where
    I: 'i,
    C: parser::Parser<'i, I, E>,
    S: recovery::Strategy<'i, I, C, E>,
    E: error::Error<'i, I>,
{
    type Output = C::Output;

    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, E::Location>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
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
        /*let parser = just(&'a').boxed();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['b', 'c']
        );*/
    }

    #[test]
    fn test_to() {
        let parser = Parser::<_>::to(just(&'a'), 42usize);
        let mut stream = Parser::<_>::stream(&parser, &['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(42usize)));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    #[test]
    fn test_map() {
        let parser = Parser::<_>::map(just(&'a'), |x| x.to_ascii_uppercase());
        let mut stream = Parser::<_>::stream(&parser, &['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success('A')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }

    #[test]
    fn test_map_with_span() {
        let parser = Parser::<_>::map_with_span(just(&'a'), |x, s| (x.to_ascii_uppercase(), s));
        let mut stream = Parser::<_>::stream(&parser, &['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(('A', 0..1))));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);
    }
}
