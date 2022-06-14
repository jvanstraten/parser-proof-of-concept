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
    /// (may also simply be 0 if nothing matched), and a single error message.
    Failed(usize, E),
}

impl<O, E> From<Result<O, E>> for std::result::Result<O, E> {
    fn from(result: Result<O, E>) -> Self {
        match result {
            Result::Success(o) => Ok(o),
            Result::Recovered(_, mut es) => Err(es.drain(..).next().unwrap()),
            Result::Failed(_, e) => Err(e),
        }
    }
}

/// Main parser trait.
///
///  - 'i: lifetime of the input tokens
///  - I: type of an input token
///  - L: location tracker instance
///  - E: error type
pub trait Parser<'i, I, L, E, T>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    T: Iterator<Item = &'i I>,
{
    /// The type returned by the parser.
    type Output;

    /// The inner parsing function, to be implemented by parsers.
    ///
    /// If enable_recovery is false, must:
    ///  - return (Ok(O), vec![]) for success, where O is the parse tree,
    ///    leaving the stream cursor at the end of the parsed input; or
    ///  - return (Err(i), vec![E, ...]) for failure, where i is the index of
    ///    the last token that was successfully parsed or 0 if none, and E is
    ///    at least one error, leaving the stream cursor unchanged/where
    ///    parsing started.
    ///
    /// If enable_recovery is true, semantics are the same, except that errors
    /// may be returned for Ok results as well. Successful recovery is
    /// (Ok(), vec![E, ...]).
    fn parse_internal(
        &self,
        stream: &mut stream::Stream<'i, I, L, T>,
        enable_recovery: bool,
    ) -> Result<Self::Output, E>;

    /// Parse the given source of tokens, starting from the given location.
    /// Return the (potentially recovered) parse tree and the list of errors
    /// produced while parsing.
    fn parse_with_recovery_and_location(
        &self,
        source: impl IntoIterator<Item = &'i I, IntoIter = T>,
        start_location: L,
    ) -> Result<Self::Output, E> {
        let mut stream = stream::Stream::new_with_location(source, start_location);
        self.parse_internal(&mut stream, true)
    }

    /// Parse the given source of tokens, starting from the given location.
    /// Return the parse tree or the first error.
    fn parse_with_location(
        &self,
        source: impl IntoIterator<Item = &'i I, IntoIter = T>,
        start_location: L,
    ) -> std::result::Result<Self::Output, E> {
        self.parse_with_recovery_and_location(source, start_location)
            .into()
    }

    /// Parse the given source of tokens. Return the (potentially recovered)
    /// parse tree and the list of errors produced while parsing.
    fn parse_with_recovery(
        &self,
        source: impl IntoIterator<Item = &'i I, IntoIter = T>,
    ) -> Result<Self::Output, E>
    where
        L: Default,
    {
        self.parse_with_recovery_and_location(source, L::default())
    }

    /// Parse the given source of tokens. Return the parse tree or the first
    /// error.
    fn parse(
        &self,
        source: impl IntoIterator<Item = &'i I, IntoIter = T>,
    ) -> std::result::Result<Self::Output, E>
    where
        L: Default,
    {
        self.parse_with_recovery(source).into()
    }
    // TODO combinators a la Chumsky
}
