// SPDX-License-Identifier: Apache-2.0

use std::marker::PhantomData;

use super::error;
use super::location;
use super::parser;
use super::scanner;
use super::stream;

/// Trait for recovery strategies.
pub trait Recover<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    /// Called when the given `parser` has failed to parse the input in
    /// `stream` starting from `started_at`. `failed_at` is initially set to
    /// the position of the token where parsing fails, and `errors` is
    /// initially set to the list of errors returned by the parser. If the
    /// recovery strategy succeeds, it should return Some(output); if it fails,
    /// it should return None. In either case, the contents of `errors` after
    /// the call are used as the final error list; the recovery strategy may
    /// add to, remove from, or otherwise mutate this list in order to increase
    /// the quality of the error messages.
    ///
    /// The combinators provided by the crate all implement the following
    /// pattern: first try the child strategy (the one it was constructed
    /// from), and only if that fails try the strategy that the combinator
    /// represents. Thus, each combinator represents an action in a sequence,
    /// the first successful of which is used to recover. Most combinators
    /// always fail, though, and instead only modify the stream position, the
    /// error list, and/or the `failed_at` point (if it calls a parser) to set
    /// the stage for the next combinator that actually does something.
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output>;
}

/// Trait for complete recovery strategies.
pub trait Strategy<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    Self: Recover<'i, I, C>,
{
}

/// Trait for incomplete recovery strategies, that require the use of
/// combinators to complete.
pub trait IncompleteStrategy<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    Self: Recover<'i, I, C>,
{
    //-------------------------------------------------------------------------
    // Strategies that just manipulate the input stream position
    //-------------------------------------------------------------------------

    /// Backtracks to the position in the input stream where the initial parser
    /// started from.
    fn restart(self) -> Restart<Self>
    where
        Self: Sized,
    {
        Restart { child: self }
    }

    /// Seek to the token that caused the most-recently-called parser to fail,
    /// then fail recovery to hand control over to the next strategy.
    fn seek_to_failed(self) -> SeekToFailed<Self>
    where
        Self: Sized,
    {
        SeekToFailed { child: self }
    }

    /// Skip a single token. Does nothing if at EOF.
    fn skip(self) -> Skip<Self>
    where
        Self: Sized,
    {
        Skip { child: self }
    }

    /// Skips a single token if it matches the predicate. Does nothing if at EOF.
    fn skip_if<F>(self, predicate: F) -> SkipIf<Self, F>
    where
        Self: Sized,
        F: Fn(&I) -> bool,
    {
        SkipIf {
            child: self,
            predicate,
        }
    }

    /// Skip tokens until the next one matches the given filter function or EOF
    /// is reached, then fail recovery to hand control over to the next
    /// strategy.
    fn find<F>(self, predicate: F) -> Find<Self, F>
    where
        Self: Sized,
        F: Fn(&I) -> bool,
    {
        Find {
            child: self,
            predicate,
        }
    }

    /// Scans tokens using the given custom recovery logic. This behaves like
    /// skip_until(), but is capable of maintaining state between calls and can
    /// return errors. This can for example be used for intelligent
    /// parenthesis/bracket matching.
    fn scan<T, F>(self, factory: F) -> Scan<Self, F>
    where
        Self: Sized,
        T: scanner::Scanner<'i, I, C::Error>,
        F: Fn() -> T,
    {
        Scan {
            child: self,
            factory,
        }
    }

    //-------------------------------------------------------------------------
    // Strategies that branch the strategy sequence
    //-------------------------------------------------------------------------

    /// Try the given strategy. If this fails, continue from the current
    /// position, rather than from where the given strategy ended up. Errors
    /// are however maintained.
    fn maybe<T>(self, inner: T) -> Maybe<Self, T>
    where
        Self: Sized,
        T: IncompleteStrategy<'i, I, C>,
    {
        Maybe { child: self, inner }
    }

    /// While the token matcher function returns false, run the given strategy.
    /// Stop once the matcher returns true. This is like skip_until(), but with
    /// a strategy to run while skipping. Commonly used with [retry()].
    fn while_not<F, T>(self, predicate: F, inner: T) -> WhileNot<Self, F, T>
    where
        Self: Sized,
        F: Fn(&I) -> bool,
        T: IncompleteStrategy<'i, I, C>,
    {
        WhileNot {
            child: self,
            predicate,
            inner,
        }
    }

    //-------------------------------------------------------------------------
    // Strategies that run parsers to recover
    //-------------------------------------------------------------------------

    /// Retry the original parser from this position. If this fails, the stream
    /// position will be left unchanged, but the tokens that were successfully
    /// parsed by the parser before it failed can be skipped using
    /// from_failed(). By default, previously defined recovery strategies of the
    /// parser are also reattempted, but this can be disabled by calling
    /// [Retry::exactly()]. Error messages generated by the parser are added
    /// unless [Retry::silently()] is called.
    fn retry(self) -> Retry<Self>
    where
        Self: Sized,
    {
        Retry {
            child: self,
            exact: false,
            silent: false,
        }
    }

    /// Same as retry(), but uses the provided parser instead.
    fn try_to_parse<T>(self, parser: T) -> TryToParse<Self, T>
    where
        Self: Sized,
        T: parser::Parser<'i, I, Output = C::Output, Error = C::Error>,
    {
        TryToParse {
            child: self,
            parser,
            exact: false,
            silent: false,
        }
    }

    //-------------------------------------------------------------------------
    // Strategies that manipulate the error list
    //-------------------------------------------------------------------------

    /// Pushes an error.
    fn push_error<F>(self, factory: F) -> PushError<Self, F>
    where
        Self: Sized,
        F: Fn() -> C::Error,
    {
        PushError {
            child: self,
            factory,
        }
    }

    /// Pushes an error at the current location.
    fn push_error_here<F>(self, factory: F) -> PushErrorHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
        ) -> C::Error,
    {
        PushErrorHere {
            child: self,
            factory,
        }
    }

    /// Pushes an error for the span reaching from the start position up to the
    /// current position.
    fn push_error_up_to_here<F>(self, factory: F) -> PushErrorUpToHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ) -> C::Error,
    {
        PushErrorUpToHere {
            child: self,
            factory,
        }
    }

    /// Pushes an error for the next token.
    fn push_error_for_token<F>(self, factory: F) -> PushErrorForToken<Self, F>
    where
        Self: Sized,
        F: Fn(
            Option<&I>,
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ) -> C::Error,
    {
        PushErrorForToken {
            child: self,
            factory,
        }
    }

    /// Updates the list of errors using the given function.
    fn update_errors<F>(self, updater: F) -> UpdateErrors<Self, F>
    where
        Self: Sized,
        F: Fn(&mut Vec<C::Error>),
    {
        UpdateErrors {
            child: self,
            updater,
        }
    }

    /// Updates the list of errors using the given function and the current
    /// location.
    fn update_errors_here<F>(self, updater: F) -> UpdateErrorsHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            &mut Vec<C::Error>,
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
        ),
    {
        UpdateErrorsHere {
            child: self,
            updater,
        }
    }

    /// Updates the list of errors using the given function and the span
    /// reaching from the start position up to the current location.
    fn update_errors_up_to_here<F>(self, updater: F) -> UpdateErrorsUpToHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            &mut Vec<C::Error>,
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ),
    {
        UpdateErrorsUpToHere {
            child: self,
            updater,
        }
    }

    /// Updates the list of errors using the given function and the next
    /// token.
    fn update_errors_for_token<F>(self, updater: F) -> UpdateErrorsForToken<Self, F>
    where
        Self: Sized,
        F: Fn(
            &mut Vec<C::Error>,
            Option<&I>,
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ),
    {
        UpdateErrorsForToken {
            child: self,
            updater,
        }
    }

    //-------------------------------------------------------------------------
    // Misc. strategy combinators
    //-------------------------------------------------------------------------

    /// Puts the strategy in a box to restrain it to a known type.
    fn boxed(self) -> Boxed<'i, I, C>
    where
        Self: Sized + 'i,
    {
        Boxed {
            strategy: Box::new(self),
        }
    }

    /// Does nothing. You can use this when you want to recover by returning
    /// something without skipping any tokens and you want the functions to
    /// read like an English sentence; for example
    ///
    /// ```ignore
    /// parser.to_recover(attempt_to().do_nothing().and_return(...))
    /// ```
    fn do_nothing(self) -> Self
    where
        Self: Sized,
    {
        self
    }

    //-------------------------------------------------------------------------
    // Completing strategies
    //-------------------------------------------------------------------------

    /// Succeed with recovery by emitting the given output, as if the tokens
    /// from the start position up to the current stream position had been
    /// parsed into that.
    fn and_return(self, output: C::Output) -> Return<Self, C::Output>
    where
        Self: Sized,
        C::Output: Clone,
    {
        Return {
            child: self,
            output,
        }
    }

    /// Like and_return(), but uses a function to generate the output.
    fn and_return_with<F>(self, output: F) -> ReturnWith<Self, F>
    where
        Self: Sized,
        F: Fn() -> C::Output,
    {
        ReturnWith {
            child: self,
            output,
        }
    }

    /// Like and_return_with(), but the function receives the span representing
    /// the input that we're pretending to have been parsed from.
    fn and_return_with_span<F>(self, output: F) -> ReturnWithSpan<Self, F>
    where
        Self: Sized,
        F: Fn(
            <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ) -> C::Output,
    {
        ReturnWithSpan {
            child: self,
            output,
        }
    }

    /// Completes a strategy with failure if none of the preceding strategies
    /// were successful.
    fn or_fail(self) -> OrFail<Self>
    where
        Self: Sized,
    {
        OrFail { child: self }
    }
}

/// A strategy that tries nothing and is all out of ideas: it serves as a
/// starting point for constructing strategies. See [attempt_to()].
pub struct AttemptTo<I, C> {
    phantom: PhantomData<(I, C)>,
}

impl<'i, I, C> Recover<'i, I, C> for AttemptTo<I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    fn recover(
        &self,
        _parser: &C,
        _stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        _started_at: &stream::SavedState,
        _failed_at: &mut stream::SavedState,
        _errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        None
    }
}

impl<'i, I, C> IncompleteStrategy<'i, I, C> for AttemptTo<I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
}

/// Create an empty strategy that does nothing on its own. This strategy can
/// then be augmented using the combinators defined on it.
///
/// Each strategy combinator will first run the strategy it was created from.
/// This may operate on or add to the list of errors, modify the token stream
/// position, and ultimately succeed in recovery or fail. If it succeeds,
/// recovery succeeds as a whole; that is, the remainder of the combinator is
/// not run, and the current position in the token stream is where the next
/// parser will start from. Only if it fails will the combinator's behavior
/// come into play.
///
/// Note that most combinators always fail to recover on their own, and
/// instead serve to modify the stream position or error list. In particular,
/// the [Nothing] returned by this function does absolutely nothing and fails,
/// thus simply passing control to combinators applied to it.
pub fn attempt_to<I, C>() -> AttemptTo<I, C> {
    AttemptTo {
        phantom: Default::default(),
    }
}

/// See [IncompleteStrategy::restart()].
pub struct Restart<S> {
    child: S,
}

impl<'i, I, C, S> Recover<'i, I, C> for Restart<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.restore(started_at);
                None
            })
    }
}

impl<'i, I, C, S> IncompleteStrategy<'i, I, C> for Restart<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::seek_to_failed()].
pub struct SeekToFailed<S> {
    child: S,
}

impl<'i, I, C, S> Recover<'i, I, C> for SeekToFailed<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.restore(failed_at);
                None
            })
    }
}

impl<'i, I, C, S> IncompleteStrategy<'i, I, C> for SeekToFailed<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::seek_to_failed()].
pub fn seek_to_failed<'i, I, C>() -> SeekToFailed<AttemptTo<I, C>>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    attempt_to().seek_to_failed()
}

/// See [IncompleteStrategy::skip()].
pub struct Skip<S> {
    child: S,
}

impl<'i, I, C, S> Recover<'i, I, C> for Skip<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.advance();
                None
            })
    }
}

impl<'i, I, C, S> IncompleteStrategy<'i, I, C> for Skip<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::skip()].
pub fn skip<'i, I, C>() -> Skip<AttemptTo<I, C>>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    attempt_to().skip()
}

/// See [IncompleteStrategy::skip_if()].
pub struct SkipIf<S, F> {
    child: S,
    predicate: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for SkipIf<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                if stream.token().map(&self.predicate).unwrap_or(false) {
                    stream.advance();
                }
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for SkipIf<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
{
}

/// See [IncompleteStrategy::skip_if()].
pub fn skip_if<'i, I, C, F>(predicate: F) -> SkipIf<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(&I) -> bool,
{
    attempt_to().skip_if(predicate)
}

/// See [IncompleteStrategy::find()].
pub struct Find<S, F> {
    child: S,
    predicate: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for Find<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                while !stream.token().map(&self.predicate).unwrap_or(true) {
                    stream.advance();
                }
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for Find<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
{
}

/// See [IncompleteStrategy::find()].
pub fn find<'i, I, C, F>(predicate: F) -> Find<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(&I) -> bool,
{
    attempt_to().find(predicate)
}

/// See [IncompleteStrategy::scan()].
pub struct Scan<S, F> {
    child: S,
    factory: F,
}

impl<'i, I, C, S, F, T> Recover<'i, I, C> for Scan<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> T,
    T: scanner::Scanner<'i, I, C::Error>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                let mut seeker = (self.factory)();
                while match stream.token() {
                    Some(token) => !seeker.scan(token, stream.span(), errors),
                    None => {
                        seeker.eof(stream.location(), errors);
                        false
                    }
                } {
                    stream.advance();
                }
                None
            })
    }
}

impl<'i, I, C, S, F, T> IncompleteStrategy<'i, I, C> for Scan<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> T,
    T: scanner::Scanner<'i, I, C::Error>,
{
}

/// See [IncompleteStrategy::scan()].
pub fn scan<'i, I, C, F, T>(factory: F) -> Scan<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn() -> T,
    T: scanner::Scanner<'i, I, C::Error>,
{
    attempt_to().scan(factory)
}

/// See [IncompleteStrategy::maybe()].
pub struct Maybe<S, T> {
    child: S,
    inner: T,
}

impl<'i, I, C, S, T> Recover<'i, I, C> for Maybe<S, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    T: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.attempt(|stream| {
                    match self
                        .inner
                        .recover(parser, stream, started_at, failed_at, errors)
                    {
                        Some(o) => Ok(Some(o)),
                        None => Err(None),
                    }
                })
            })
    }
}

impl<'i, I, C, S, T> IncompleteStrategy<'i, I, C> for Maybe<S, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    T: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::maybe()].
pub fn maybe<'i, I, C, T>(inner: T) -> Maybe<AttemptTo<I, C>, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    T: IncompleteStrategy<'i, I, C>,
{
    attempt_to().maybe(inner)
}

/// See [IncompleteStrategy::while_not()].
pub struct WhileNot<S, F, T> {
    child: S,
    predicate: F,
    inner: T,
}

impl<'i, I, C, S, F, T> Recover<'i, I, C> for WhileNot<S, F, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
    T: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                while !stream.token().map(&self.predicate).unwrap_or(true) {
                    if let Some(result) = self
                        .inner
                        .recover(parser, stream, started_at, failed_at, errors)
                    {
                        return Some(result);
                    }
                    stream.advance();
                }
                None
            })
    }
}

impl<'i, I, C, S, F, T> IncompleteStrategy<'i, I, C> for WhileNot<S, F, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&I) -> bool,
    T: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::while_not()].
pub fn while_not<'i, I, C, F, T>(predicate: F, inner: T) -> WhileNot<AttemptTo<I, C>, F, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(&I) -> bool,
    T: IncompleteStrategy<'i, I, C>,
{
    attempt_to().while_not(predicate, inner)
}

/// See [IncompleteStrategy::retry()].
pub struct Retry<S> {
    child: S,
    exact: bool,
    silent: bool,
}

impl<S> Retry<S> {
    /// Match the given parser exactly; do NOT consider recovery strategies
    /// attached to the parser.
    pub fn exactly(mut self) -> Self {
        self.exact = true;
        self
    }

    /// Do NOT append error messages returned by the parser to the error list.
    pub fn silently(mut self) -> Self {
        self.silent = true;
        self
    }

    /// Combines exactly() and silently().
    pub fn exactly_and_silently(mut self) -> Self {
        self.exact = true;
        self.silent = true;
        self
    }
}

impl<'i, I, C, S> Recover<'i, I, C> for Retry<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| match parser.parse_internal(stream, !self.exact) {
                parser::Result::Success(o) => Some(o),
                parser::Result::Recovered(o, es) => {
                    if !self.silent {
                        errors.extend(es);
                    }
                    Some(o)
                }
                parser::Result::Failed(i, es) => {
                    if !self.silent {
                        errors.extend(es);
                    }
                    *failed_at = stream.save_at(i);
                    None
                }
            })
    }
}

impl<'i, I, C, S> IncompleteStrategy<'i, I, C> for Retry<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::try_to_parse()].
pub struct TryToParse<S, T> {
    child: S,
    parser: T,
    exact: bool,
    silent: bool,
}

impl<S, T> TryToParse<S, T> {
    /// Match the given parser exactly; do NOT consider recovery strategies
    /// attached to the parser.
    pub fn exactly(mut self) -> Self {
        self.exact = true;
        self
    }

    /// Do NOT append error messages returned by the parser to the error list.
    pub fn silently(mut self) -> Self {
        self.silent = true;
        self
    }

    /// Combines exactly() and silently().
    pub fn exactly_and_silently(mut self) -> Self {
        self.exact = true;
        self.silent = true;
        self
    }
}

impl<'i, I, C, S, T> Recover<'i, I, C> for TryToParse<S, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    T: parser::Parser<'i, I, Output = C::Output, Error = C::Error>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| match self.parser.parse_internal(stream, !self.exact) {
                parser::Result::Success(o) => Some(o),
                parser::Result::Recovered(o, es) => {
                    if !self.silent {
                        errors.extend(es);
                    }
                    Some(o)
                }
                parser::Result::Failed(i, es) => {
                    if !self.silent {
                        errors.extend(es);
                    }
                    *failed_at = stream.save_at(i);
                    None
                }
            })
    }
}

impl<'i, I, C, S, T> IncompleteStrategy<'i, I, C> for TryToParse<S, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    T: parser::Parser<'i, I, Output = C::Output, Error = C::Error>,
{
}

/// See [IncompleteStrategy::try_to_parse()].
pub fn try_to_parse<'i, I, C, T>(parser: T) -> TryToParse<AttemptTo<I, C>, T>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    T: parser::Parser<'i, I, Output = C::Output, Error = C::Error>,
{
    attempt_to().try_to_parse(parser)
}

/// See [IncompleteStrategy::push_error()].
pub struct PushError<S, F> {
    child: S,
    factory: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for PushError<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> C::Error,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)());
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for PushError<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> C::Error,
{
}

/// See [IncompleteStrategy::push_error()].
pub fn push_error<'i, I, C, F>(factory: F) -> PushError<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn() -> C::Error,
{
    attempt_to().push_error(factory)
}

/// See [IncompleteStrategy::push_error_here()].
pub struct PushErrorHere<S, F> {
    child: S,
    factory: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for PushErrorHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ) -> C::Error,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)(stream.location()));
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for PushErrorHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ) -> C::Error,
{
}

/// See [IncompleteStrategy::push_error_here()].
pub fn push_error_here<'i, I, C, F>(factory: F) -> PushErrorHere<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ) -> C::Error,
{
    attempt_to().push_error_here(factory)
}

/// See [IncompleteStrategy::push_error_up_to_here()].
pub struct PushErrorUpToHere<S, F> {
    child: S,
    factory: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for PushErrorUpToHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)(stream.spanning_back_to(started_at)));
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for PushErrorUpToHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
}

/// See [IncompleteStrategy::push_error_up_to_here()].
pub fn push_error_up_to_here<'i, I, C, F>(factory: F) -> PushErrorUpToHere<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    attempt_to().push_error_up_to_here(factory)
}

/// See [IncompleteStrategy::push_error_for_token()].
pub struct PushErrorForToken<S, F> {
    child: S,
    factory: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for PushErrorForToken<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)(stream.token(), stream.span()));
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for PushErrorForToken<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
}

/// See [IncompleteStrategy::push_error_for_token()].
pub fn push_error_for_token<'i, I, C, F>(factory: F) -> PushErrorForToken<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    attempt_to().push_error_for_token(factory)
}

/// See [IncompleteStrategy::update_errors()].
pub struct UpdateErrors<S, F> {
    child: S,
    updater: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for UpdateErrors<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&mut Vec<C::Error>),
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors);
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for UpdateErrors<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(&mut Vec<C::Error>),
{
}

/// See [IncompleteStrategy::update_errors()].
pub fn update_errors<'i, I, C, F>(updater: F) -> UpdateErrors<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(&mut Vec<C::Error>),
{
    attempt_to().update_errors(updater)
}

/// See [IncompleteStrategy::update_errors_here()].
pub struct UpdateErrorsHere<S, F> {
    child: S,
    updater: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for UpdateErrorsHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ),
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors, stream.location());
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for UpdateErrorsHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ),
{
}

/// See [IncompleteStrategy::update_errors_here()].
pub fn update_errors_here<'i, I, C, F>(updater: F) -> UpdateErrorsHere<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ),
{
    attempt_to().update_errors_here(updater)
}

/// See [IncompleteStrategy::update_errors_up_to_here()].
pub struct UpdateErrorsUpToHere<S, F> {
    child: S,
    updater: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for UpdateErrorsUpToHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors, stream.spanning_back_to(started_at));
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for UpdateErrorsUpToHere<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
}

/// See [IncompleteStrategy::update_errors_up_to_here()].
pub fn update_errors_up_to_here<'i, I, C, F>(updater: F) -> UpdateErrorsUpToHere<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
    attempt_to().update_errors_up_to_here(updater)
}

/// See [IncompleteStrategy::update_errors_for_token()].
pub struct UpdateErrorsForToken<S, F> {
    child: S,
    updater: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for UpdateErrorsForToken<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors, stream.token(), stream.span());
                None
            })
    }
}

impl<'i, I, C, S, F> IncompleteStrategy<'i, I, C> for UpdateErrorsForToken<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        &mut Vec<C::Error>,
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
}

/// See [IncompleteStrategy::update_errors_for_token()].
pub fn update_errors_for_token<'i, I, C, F>(updater: F) -> UpdateErrorsForToken<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        &mut Vec<C::Error>,
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ),
{
    attempt_to().update_errors_for_token(updater)
}

/// See [IncompleteStrategy::boxed()].
pub struct Boxed<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    pub(crate) strategy: Box<dyn IncompleteStrategy<'i, I, C> + 'i>,
}

impl<'i, I, C> Recover<'i, I, C> for Boxed<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.strategy
            .recover(parser, stream, started_at, failed_at, errors)
    }
}

impl<'i, I, C> IncompleteStrategy<'i, I, C> for Boxed<'i, I, C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
}

/// See [IncompleteStrategy::and_return()].
pub struct Return<S, O> {
    child: S,
    output: O,
}

impl<'i, I, C, S> Recover<'i, I, C> for Return<S, C::Output>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    C::Output: Clone,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| Some(self.output.clone()))
    }
}

impl<'i, I, C, S> Strategy<'i, I, C> for Return<S, C::Output>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    C::Output: Clone,
    S: IncompleteStrategy<'i, I, C>,
{
}

/// See [IncompleteStrategy::and_return()].
pub fn just_return<'i, I, C>(output: C::Output) -> Return<AttemptTo<I, C>, C::Output>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    C::Output: Clone,
{
    attempt_to().do_nothing().and_return(output)
}

/// See [IncompleteStrategy::and_return_with()].
pub struct ReturnWith<S, F> {
    child: S,
    output: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for ReturnWith<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> C::Output,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| Some((self.output)()))
    }
}

impl<'i, I, C, S, F> Strategy<'i, I, C> for ReturnWith<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn() -> C::Output,
{
}

/// See [IncompleteStrategy::and_return_with()].
pub fn just_return_with<'i, I, C, F>(output: F) -> ReturnWith<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn() -> C::Output,
{
    attempt_to().do_nothing().and_return_with(output)
}

/// See [IncompleteStrategy::and_return_with_span()].
pub struct ReturnWithSpan<S, F> {
    child: S,
    output: F,
}

impl<'i, I, C, S, F> Recover<'i, I, C> for ReturnWithSpan<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Output,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
            .or_else(|| Some((self.output)(stream.spanning_back_to(started_at))))
    }
}

impl<'i, I, C, S, F> Strategy<'i, I, C> for ReturnWithSpan<S, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Output,
{
}

/// See [IncompleteStrategy::and_return_with_span()].
pub fn just_return_with_span<'i, I, C, F>(output: F) -> ReturnWithSpan<AttemptTo<I, C>, F>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Output,
{
    attempt_to().do_nothing().and_return_with_span(output)
}

/// See [IncompleteStrategy::or_fail()].
pub struct OrFail<S> {
    child: S,
}

impl<'i, I, C, S> Recover<'i, I, C> for OrFail<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
    fn recover(
        &self,
        parser: &C,
        stream: &mut stream::Stream<'i, I, <C::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<C::Error>,
    ) -> Option<C::Output> {
        self.child
            .recover(parser, stream, started_at, failed_at, errors)
    }
}

impl<'i, I, C, S> Strategy<'i, I, C> for OrFail<S>
where
    I: 'i,
    C: parser::Parser<'i, I>,
    S: IncompleteStrategy<'i, I, C>,
{
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn test_null_recovery() {
        let parser = just(&'a')
            .to_recover(just_return(&'a'))
            .with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);

        let mut stream = parser.stream(&['c', 'b', 'a']);
        assert!(matches!(
            stream.next(),
            Some(ParseResult::Recovered(&'a', _))
        ));
        assert_eq!(
            stream.tail().cloned().collect::<Vec<_>>(),
            vec!['c', 'b', 'a']
        );
    }
}
