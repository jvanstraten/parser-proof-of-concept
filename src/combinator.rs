use super::algorithm;
use super::error;
use super::location;
use super::parser;
use super::primitive;

/// See [parser::Parser::boxed()].
pub struct Boxed<'i, I, O, L, E> {
    pub(crate) parser: Box<dyn parser::Parser<'i, I, L, E, Output = O> + 'i>,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for Boxed<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, O, L, E, C> parser::Parser<'i, I, L, E> for To<C, O>
where
    I: 'i,
    O: Clone,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, O, L, E, C> parser::Parser<'i, I, L, E> for Some<C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = O>,
{
    type Output = Option<O>;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for Map<C, F>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
    F: Fn(A) -> O,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for MapWithSpan<C, F>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
    F: Fn(A, L::Span) -> O,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, F, L, E, C> parser::Parser<'i, I, L, E> for MapErr<C, F, A>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A>,
    F: Fn(A) -> E,
{
    type Output = C::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, F, L, E, C> parser::Parser<'i, I, L, E> for MapErrWithSpan<C, F, A>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A>,
    F: Fn(A, L::Span) -> E,
{
    type Output = C::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for TryMap<C, F>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
    F: Fn(A, L::Span) -> TryMapResult<O, E>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, L, E, A, B> parser::Parser<'i, I, L, E> for Then<A, B>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
    B: parser::Parser<'i, I, L, E>,
{
    type Output = (A::Output, B::Output);

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, L, E, A, B> parser::Parser<'i, I, L, E> for ThenIgnore<A, B>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
    B: parser::Parser<'i, I, L, E>,
{
    type Output = A::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, L, E, A, B> parser::Parser<'i, I, L, E> for IgnoreThen<A, B>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
    B: parser::Parser<'i, I, L, E>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, L, E, A, B, C> parser::Parser<'i, I, L, E> for DelimitedBy<A, B, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
    B: parser::Parser<'i, I, L, E>,
    C: parser::Parser<'i, I, L, E>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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

impl<'i, I, L, E, A, B> parser::Parser<'i, I, L, E> for PaddedBy<A, B>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
    B: parser::Parser<'i, I, L, E>,
{
    type Output = B::Output;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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
pub struct Chain<'i, I, O, L, E> {
    pub(crate) parsers: Vec<Boxed<'i, I, O, L, E>>,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for Chain<'i, I, O, L, E>
where
    I: 'i,
    O: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = Vec<O>;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        algorithm::concatenate(stream, enable_recovery, &self.parsers)
    }
}

impl<'i, I, O, L, E> Chain<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    /// Append an additional parser to this chain.
    pub fn and<B>(self, other: B) -> Chain<'i, I, O, L, E>
    where
        B: parser::Parser<'i, I, L, E, Output = O> + 'i,
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

impl<'i, I, O, L, E, A, B> parser::Parser<'i, I, L, E> for Or<A, B>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E, Output = O>,
    B: parser::Parser<'i, I, L, E, Output = O>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        alternate!(stream, enable_recovery, &self.a, &self.b)
    }
}

/// See [parser::Parser::or_not()].
pub struct OrNot<A> {
    pub(crate) a: Some<A>,
}

impl<'i, I, O, L, E, A> parser::Parser<'i, I, L, E> for OrNot<A>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E, Output = O>,
{
    type Output = Option<O>;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        alternate!(stream, enable_recovery, &self.a, &primitive::none::<O>())
    }
}

/// See [parser::Parser::chain_alternatives()].
pub struct ChainAlternatives<'i, I, O, L, E> {
    pub(crate) parsers: Vec<Boxed<'i, I, O, L, E>>,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for ChainAlternatives<'i, I, O, L, E>
where
    I: 'i,
    O: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        algorithm::alternate(stream, enable_recovery, &self.parsers)
    }
}

impl<'i, I, O, L, E> ChainAlternatives<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    /// Append an additional parser to this chain.
    pub fn and<B>(self, other: B) -> Chain<'i, I, O, L, E>
    where
        B: parser::Parser<'i, I, L, E, Output = O> + 'i,
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

impl<'i, I, L, E, A> parser::Parser<'i, I, L, E> for Repeated<A>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    A: parser::Parser<'i, I, L, E>,
{
    type Output = Vec<A::Output>;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
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
