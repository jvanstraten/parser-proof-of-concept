use super::error;
use super::location;
use super::parser;

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

macro_rules! concat_parsers {
    ($stream:expr, $enable_recovery:expr, $map:expr, $first:expr, $($other:expr),*) => {{
        // Store the initial state, which we'll need to restore if the first
        // parser succeeds but the second fails.
        let initial = $stream.save();

        // Set to Some(errors) when a child parser recovered from a parse
        // error.
        let mut recovery = None;

        // Construct a tuple of the outputs as we parse.
        let o = (

            // Parse the first child.
            match $first.parse_internal($stream, $enable_recovery) {
                parser::Result::Success(a) => a,
                parser::Result::Recovered(a, es_a) => {
                    recovery = Some(es_a);
                    a
                }
                parser::Result::Failed(i, es) => {
                    // No need to restore state, because the only parser we ran
                    // failed.
                    return parser::Result::Failed(i, es);
                }
            },

            $(
                // Parse the other children.
                match $other.parse_internal($stream, $enable_recovery) {
                    parser::Result::Success(b) => b,
                    parser::Result::Recovered(b, es_b) => {
                        if let Some(es) = &mut recovery {
                            es.extend(es_b);
                        } else {
                            recovery = Some(es_b);
                        }
                        b
                    }
                    parser::Result::Failed(i, es) => {
                        // Need to restore the state here, previous  parsers
                        // will have mutated it.
                        $stream.restore(&initial);
                        return parser::Result::Failed(i, es);
                    }
                },
            )*

        );

        // Map the tuple according to the map function.
        let map = $map;
        let o = map(o);

        // Return success or recovered based on whether any of the parsers
        // resovered.
        if let Some(es) = recovery {
            assert!($enable_recovery);
            parser::Result::Recovered(o, es)
        } else {
            parser::Result::Success(o)
        }
    }};
}

/// See [parser::Parser::boxed()].
pub struct Boxed<'i, I, O, L, E> {
    pub parser: Box<dyn parser::Parser<'i, I, L, E, Output = O> + 'i>,
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
        concat_parsers!(stream, enable_recovery, |x| x, self.a, self.b)
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
        concat_parsers!(stream, enable_recovery, |(a, _b)| a, self.a, self.b)
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
        concat_parsers!(stream, enable_recovery, |(_a, b)| b, self.a, self.b)
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
        concat_parsers!(
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
        concat_parsers!(
            stream,
            enable_recovery,
            |(_l, m, _r)| m,
            self.padding,
            self.middle,
            self.padding
        )
    }
}
