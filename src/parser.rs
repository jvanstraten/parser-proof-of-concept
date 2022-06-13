use super::location;
use super::stream;

/// Result of a single parsing step. The first element is the result of the
/// parser; it will be None if parsing and recovery (if enabled) failed.
/// The second element is the set of errors produced thus far.
pub type Result<O, E> = (Option<O>, Vec<E>);

pub trait Parser<I, O, L, E>
where
    L: location::LocationTracker<I>,
{
    /// The inner parsing function, to be implemented by parsers.
    ///
    /// If enable_recovery is false, must:
    ///  - return (Some(O), vec![]) for success, or
    ///  - return (None, vec![E, ...]) for failure.
    ///
    /// If enable_recovery is true, must:
    ///  - return (Some(O), vec![...]) for successful parsing or recovery, or
    ///  - return (None, vec![E, ...]) for failure to recover.
    fn parse_internal(
        &self,
        stream: &mut stream::Stream<I, L>,
        enable_recovery: bool,
    ) -> Result<O, E>;

    /// Parse the given source of tokens. Return the parse tree or the first
    /// error.
    fn parse<J>(&self, source: J) -> std::result::Result<O, E>
    where
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
        L: Default,
    {
        let mut stream = stream::Stream::new(source);
        let (output, mut errors) = self.parse_internal(&mut stream, false);
        output.ok_or_else(|| errors.drain(..).next().unwrap())
    }

    /// Parse the given source of tokens. Return the (potentially recovered)
    /// parse tree and the list of errors produced while parsing.
    fn parse_with_recovery<J>(&self, source: J) -> Result<O, E>
    where
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
        L: Default,
    {
        let mut stream = stream::Stream::new(source);
        self.parse_internal(&mut stream, true)
    }

    /// Parse the given source of tokens, starting from the given location.
    /// Return the parse tree or the first error.
    fn parse_with_location<J>(&self, source: J, start_location: L) -> std::result::Result<O, E>
    where
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
    {
        let mut stream = stream::Stream::new_with_location(source, start_location);
        let (output, mut errors) = self.parse_internal(&mut stream, false);
        output.ok_or_else(|| errors.drain(..).next().unwrap())
    }

    /// Parse the given source of tokens, starting from the given location.
    /// Return the (potentially recovered) parse tree and the list of errors
    /// produced while parsing.
    fn parse_with_recovery_and_location<J>(&self, source: J, start_location: L) -> Result<O, E>
    where
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
    {
        let mut stream = stream::Stream::new_with_location(source, start_location);
        self.parse_internal(&mut stream, true)
    }

    // TODO combinators a la Chumsky
}
