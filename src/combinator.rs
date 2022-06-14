use super::error;
use super::location;
use super::parser;

/// See [parser::Parser::map()].
///
///  - 'i: lifetime of input tokens
///  - I: type of input tokens
///  - A: output of child parser, input of map
///  - O: output of map
///  - F: function mapping A to O
///  - L: location tracker type
///  - E: error type
///  - C: child parser type
pub struct Map<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
    F: Fn(A) -> O,
{
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<(&'i I, A, O, L, E)>,
}

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for Map<'i, I, A, O, F, L, E, C>
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
///
///  - 'i: lifetime of input tokens
///  - I: type of input tokens
///  - A: output of child parser, input of map
///  - O: output of map
///  - F: function mapping A to O
///  - L: location tracker type
///  - E: error type
///  - C: child parser type
pub struct MapWithSpan<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, E, Output = A>,
    F: Fn(A, L::Span) -> O,
{
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<(&'i I, A, O, L, E)>,
}

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for MapWithSpan<'i, I, A, O, F, L, E, C>
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
///
///  - 'i: lifetime of input tokens
///  - I: type of input tokens
///  - A: error type of child parser, input of map
///  - O: output type
///  - F: function mapping A to O
///  - L: location tracker type
///  - E: output error type
///  - C: child parser type
pub struct MapErr<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A, Output = O>,
    F: Fn(A) -> E,
{
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<(&'i I, A, O, L, E)>,
}

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E> for MapErr<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A, Output = O>,
    F: Fn(A) -> E,
{
    type Output = O;

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
///
///  - 'i: lifetime of input tokens
///  - I: type of input tokens
///  - A: error type of child parser, input of map
///  - O: output type
///  - F: function mapping A to O
///  - L: location tracker type
///  - E: output error type
///  - C: child parser type
pub struct MapErrWithSpan<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A, Output = O>,
    F: Fn(A, L::Span) -> E,
{
    pub(crate) child: C,
    pub(crate) map: F,
    pub(crate) phantom: std::marker::PhantomData<(&'i I, A, O, L, E)>,
}

impl<'i, I, A, O, F, L, E, C> parser::Parser<'i, I, L, E>
    for MapErrWithSpan<'i, I, A, O, F, L, E, C>
where
    I: 'i,
    L: location::LocationTracker<I>,
    A: error::Error<'i, I, L>,
    E: error::Error<'i, I, L>,
    C: parser::Parser<'i, I, L, A, Output = O>,
    F: Fn(A, L::Span) -> E,
{
    type Output = O;

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
