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
        match self.child.parse_internal(stream, enable_recovery) {
            parser::Result::Success(o) => {
                parser::Result::Success((self.map)(o, stream.spanning_back_to(&from)))
            }
            parser::Result::Recovered(o, es) => {
                parser::Result::Recovered((self.map)(o, stream.spanning_back_to(&from)), es)
            }
            parser::Result::Failed(i, e) => parser::Result::Failed(i, e),
        }
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
        match self.child.parse_internal(stream, enable_recovery) {
            parser::Result::Success(o) => parser::Result::Success(o),
            parser::Result::Recovered(o, es) => parser::Result::Recovered(
                o,
                es.into_iter()
                    .map(|e| (self.map)(e, stream.spanning_back_to(&from)))
                    .collect(),
            ),
            parser::Result::Failed(i, e) => {
                parser::Result::Failed(i, (self.map)(e, stream.spanning_back_to(&from)))
            }
        }
    }
}
