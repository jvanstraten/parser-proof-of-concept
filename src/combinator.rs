use super::error;
use super::location;
use super::parser;

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
