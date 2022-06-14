use super::combinator;
use super::error;
use super::location;
use super::stream;

/// Result of a parser.
pub enum Result<O, E> {
    /// Parsing was successful, yielding the given output.
    Success(O),

    /// Parsing failed, but recovery was enabled and this succeeded, yielding
    /// recovered output and a nonempty list of errors.
    Recovered(O, Vec<E>),

    /// Parsing failed, and recovery was either disabled or also failed,
    /// yielding the index of the last token that was parsed successfully
    /// (may also simply be 0 if nothing matched), and a nonempty list of
    /// errors.
    Failed(usize, Vec<E>),
}

impl<O, E> From<Result<O, E>> for std::result::Result<O, E>
where
    E: error::Fallback,
{
    fn from(result: Result<O, E>) -> Self {
        match result {
            Result::Success(o) => Ok(o),
            Result::Recovered(_, mut es) => Err(es
                .drain(..)
                .next()
                .unwrap_or_else(|| E::fallback("unknown error"))),
            Result::Failed(_, mut es) => Err(es
                .drain(..)
                .next()
                .unwrap_or_else(|| E::fallback("unknown error"))),
        }
    }
}

impl<O, E> Result<O, E> {
    /// Returns whether parsing was successful.
    pub fn is_ok(&self) -> bool {
        matches!(self, Result::Success(_))
    }

    /// Returns the parse tree, if one is available.
    pub fn tree(&self) -> Option<&O> {
        match self {
            Result::Success(o) => Some(o),
            Result::Recovered(o, _) => Some(o),
            Result::Failed(_, _) => None,
        }
    }

    /// Returns an iterator over the errors in the result.
    pub fn errors(&self) -> ErrorIter<E> {
        match self {
            Result::Success(_) => ErrorIter::None,
            Result::Recovered(_, es) => ErrorIter::Many(es, 0),
            Result::Failed(_, es) => ErrorIter::Many(es, 0),
        }
    }

    /// Maps the tree from one type to another.
    pub fn map<X, F: FnOnce(O) -> X>(self, map: F) -> Result<X, E> {
        match self {
            Result::Success(o) => Result::Success(map(o)),
            Result::Recovered(o, es) => Result::Recovered(map(o), es),
            Result::Failed(i, es) => Result::Failed(i, es),
        }
    }

    /// Maps the errors from one type to another.
    pub fn map_err<X, F: FnMut(E) -> X>(self, map: F) -> Result<O, X> {
        match self {
            Result::Success(o) => Result::Success(o),
            Result::Recovered(o, es) => Result::Recovered(o, es.into_iter().map(map).collect()),
            Result::Failed(i, es) => Result::Failed(i, es.into_iter().map(map).collect()),
        }
    }

    /// Maps the tree from one type to another, in a way that may fail.
    pub fn try_map<X, F: FnOnce(O) -> Result<X, E>>(self, map: F) -> Result<X, E> {
        match self {
            Result::Success(o) => map(o),
            Result::Recovered(o, mut es) => match map(o) {
                Result::Success(x) => Result::Success(x),
                Result::Recovered(x, es2) => {
                    es.extend(es2);
                    Result::Recovered(x, es)
                }
                Result::Failed(i, es2) => {
                    es.extend(es2);
                    Result::Failed(i, es)
                }
            },
            Result::Failed(i, e) => Result::Failed(i, e),
        }
    }
}

/// Iterator over the errors in a [Result].
pub enum ErrorIter<'e, E> {
    None,
    Many(&'e [E], usize),
}

impl<'e, E> Iterator for ErrorIter<'e, E> {
    type Item = &'e E;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ErrorIter::None => None,
            ErrorIter::Many(es, i) => {
                if *i >= es.len() {
                    None
                } else {
                    let j = *i;
                    *i += 1;
                    Some(&es[j])
                }
            }
        }
    }
}

/// Main parser trait.
///
///  - 'i: lifetime of the input tokens
///  - I: type of an input token
///  - L: location tracker instance
///  - E: error type
pub trait Parser<'i, I, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    /// The parse tree type returned by the parser.
    type Output;

    /// The inner parsing function, to be implemented by parsers.
    ///
    /// If enable_recovery is false, must:
    ///  - return Success(O) for success, where O is the parse tree, leaving
    ///    the stream cursor at the end of the parsed input; or
    ///  - return Failed(i, E) for failure, where i is the index of the last
    ///    token that was successfully parsed or 0 if none, and E is the error
    ///    that occurred, leaving the stream cursor unchanged/where parsing
    ///    started.
    ///
    /// If enable_recovery is true, above semantics are the same, except in
    /// case of a parse error the parser may attempt to recover and:
    ///  - return Recovered(O, Vec<E>)
    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> Result<Self::Output, E>;

    /// Parse the given source of tokens, starting from the given location.
    /// Return the (potentially recovered) parse tree and the list of errors
    /// produced while parsing.
    fn parse_with_recovery_and_location<J>(
        &self,
        source: J,
        start_location: L,
    ) -> Result<Self::Output, E>
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
        Self: Sized,
    {
        let mut stream = stream::Stream::new_with_location(source, start_location);
        self.parse_internal(&mut stream, true)
    }

    /// Parse the given source of tokens, starting from the given location.
    /// Return the parse tree or the first error.
    fn parse_with_location<J>(
        &self,
        source: J,
        start_location: L,
    ) -> std::result::Result<Self::Output, E>
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
        Self: Sized,
    {
        self.parse_with_recovery_and_location(source, start_location)
            .into()
    }

    /// Parse the given source of tokens. Return the (potentially recovered)
    /// parse tree and the list of errors produced while parsing.
    fn parse_with_recovery<J>(&self, source: J) -> Result<Self::Output, E>
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
        L: Default,
        Self: Sized,
    {
        self.parse_with_recovery_and_location(source, L::default())
    }

    /// Parse the given source of tokens. Return the parse tree or the first
    /// error.
    fn parse<J>(&self, source: J) -> std::result::Result<Self::Output, E>
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
        L: Default,
        Self: Sized,
    {
        self.parse_with_recovery(source).into()
    }

    /// Maps the output of the current parser to clones of the given object.
    /// Simply pass an immutable reference to avoid cloning.
    fn to<O>(self, to: O) -> combinator::To<Self, O>
    where
        O: Clone,
        Self: Sized,
    {
        combinator::To { child: self, to }
    }

    /// Maps the output of the current parser to ().
    fn ignored<O>(self) -> combinator::Ignored<Self>
    where
        Self: Sized,
    {
        combinator::To {
            child: self,
            to: (),
        }
    }

    /// Maps the output type of the current parser to a different type using
    /// the given function.
    fn map<O, F>(self, map: F) -> combinator::Map<Self, F>
    where
        F: Fn(Self::Output) -> O,
        Self: Sized,
    {
        combinator::Map { child: self, map }
    }

    /// Maps the output type of the current parser along with the span of
    /// tokens that it matched to a different type using the given function.
    fn map_with_span<O, F>(self, map: F) -> combinator::MapWithSpan<Self, F>
    where
        F: Fn(Self::Output, L::Span) -> O,
        Self: Sized,
    {
        combinator::MapWithSpan { child: self, map }
    }

    /// Maps the error type of the current parser to a different type using
    /// the given function.
    fn map_err<X, F>(self, map: F) -> combinator::MapErr<Self, F, E>
    where
        F: Fn(E) -> X,
        X: error::Error<'i, I, L>,
        Self: Sized,
    {
        combinator::MapErr {
            child: self,
            map,
            phantom: Default::default(),
        }
    }

    /// Maps the error type of the current parser along with the span of
    /// tokens that it matched to a different type using the given function.
    fn map_err_with_span<X, F>(self, map: F) -> combinator::MapErrWithSpan<Self, F, E>
    where
        F: Fn(E, L::Span) -> X,
        X: error::Error<'i, I, L>,
        Self: Sized,
    {
        combinator::MapErrWithSpan {
            child: self,
            map,
            phantom: Default::default(),
        }
    }

    /// Maps the output type of the current parser along with the span of
    /// tokens that it matched to a different type and/or errors using the
    /// given function.
    ///
    /// The result type ([combinator::TryMapResult]) is more powerful than the
    /// typical [std::result::Result]: it allows multiple errors to be
    /// specified at once, and also allows errors that were recovered from to
    /// be specified.
    ///
    /// Note: pretty sure this also replaces Chumsky's validate().
    fn try_map<O, F>(self, map: F) -> combinator::TryMap<Self, F>
    where
        F: Fn(Self::Output, L::Span) -> combinator::TryMapResult<O, E>,
        Self: Sized,
    {
        combinator::TryMap { child: self, map }
    }

    /// Returns this parser in a box, giving a consistent type regardless of
    /// the contained parser.
    fn boxed(self) -> combinator::Boxed<'i, I, Self::Output, L, E>
    where
        Self: Sized + 'i,
    {
        combinator::Boxed {
            parser: Box::new(self),
        }
    }

    /// Parses the concatenation of the current and the given parser, yielding
    /// their results as a two-tuple.
    fn then<B>(self, b: B) -> combinator::Then<Self, B>
    where
        B: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::Then { a: self, b }
    }

    /// Parses the concatenation of the current and the given parser, yielding
    /// the result of the first one.
    fn then_ignore<B>(self, b: B) -> combinator::ThenIgnore<Self, B>
    where
        B: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::ThenIgnore { a: self, b }
    }

    /// Parses the concatenation of the current and the given parser, yielding
    /// the result of the second one.
    fn ignore_then<B>(self, b: B) -> combinator::IgnoreThen<Self, B>
    where
        B: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::IgnoreThen { a: self, b }
    }

    /// Parses the concatenation of the left, current, and right parsers,
    /// yielding the result of the current one.
    fn delimited_by<A, B>(self, left: A, right: B) -> combinator::DelimitedBy<A, Self, B>
    where
        A: Parser<'i, I, L, E>,
        B: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::DelimitedBy {
            left,
            middle: self,
            right,
        }
    }

    /// Parses the concatenation of the padding, current, and padding (again)
    /// parsers, yielding the result of the current one.
    fn padded_by<A>(self, padding: A) -> combinator::PaddedBy<A, Self>
    where
        A: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::PaddedBy {
            padding,
            middle: self,
        }
    }
    /*
    /// Parses the concatenation of the current and given parser, returning the
    /// two results as an array. The return types of the two parsers must thus
    /// match. Consecutive calls to array() will extend the array.
    fn array<A>(self, other: A) -> combinator::Array<A, 2>
    where
        A: Parser<'i, I, L, E>,
        Self: Sized,
    {
        combinator::Array {
            parsers: vec![self, other],
            middle: self,
        }
    }*/
}
