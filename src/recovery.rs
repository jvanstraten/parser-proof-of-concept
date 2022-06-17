// SPDX-License-Identifier: Apache-2.0

/*
NOTES:

Parser::to_recover() -> Strategy
    Just runs the child parser, but returns a strategy object to build a
    recovery method.

to_recover() -> Strategy
    A more descriptive shorthand for fail().to_recover(), where fail() is a
    parser that always silently fails to parse. All builtin strategies also
    have functions that further condence to_recover().<strategy>() to just
    <strategy>().

## Recovery strategies

Strategies are run when a preceding parser fails to attempt to recover from the
parse error. The provided strategies are combinator-based building blocks that
can be used to create complex recovery methods.

Each strategy follows this pattern:
 - attempt to parse or recover with the parser or strategy it was built from;
 - (only) if the above fails, attempt to recover using the logic defined by
   the recovery type.

When run, a strategy may mutate the current parser state at will. This
includes:
 - the position in the input stream;
 - the "failure point," a special position in the input stream designating the
   place where the previously called parser failed;
 - the list of errors produced by the parser being recovered from and previous
   strategies;

Most of the strategies only affect one thing at a time.

### Strategies that just manipulate the input stream position

[Strategy::]restart() -> Strategy
    Backtracks to the position in the input stream where the initial parser
    started from.

[Strategy::]seek_to_failed() -> Strategy
    Seek in the input stream to get to the point where the previous parser
    failed.

[Strategy::]skip() -> Strategy
    Skips a single token unconditionally.

[Strategy::]skip_if(|&I| -> bool) -> Strategy
    Skips a single token if it matches the predicate.

[Strategy::]find(|&I| -> bool) -> Strategy
    Skips tokens until the next token matches the given predicate or EOF is
    reached.

[Strategy::]while_not(|&I| -> bool, Strategy) -> Strategy
    Skips tokens until the next token matches the given predicate or EOF is
    reached. Whenever the predicate fails, tries to recover with the given
    strategy.

### Strategies that run parsers

[Strategy::]retry() -> Strategy
    Tries to run the child parser again. Only makes sense when this is done
    from a different position in the input stream.

[Strategy::]maybe(Parser) -> Strategy
    Tries to recover with the given parser or recovery method. In the latter
    case, failing recovery backtracks to where parsing started. The parser
    failure point is adjusted, so calling seek_to_failed() afterward will
    advance the input stream to wherever the parser failed.

### Strategies that run scanners

[Strategy::]scan(|| Scanner) -> Strategy
    Runs a scanner. This is effectively Strategy::find(), but using a
    customizable trait that can also maintain state, yield errors, and do
    something upon EOF. The provided function acts as a factory for the
    object, in order to set its initial state.

### Strategies that manipulate the error list

[Strategy::]push_error(|| -> E) -> Strategy
    Pushes an error constructed with the given factory.

[Strategy::]push_error_here(|location| -> E) -> Strategy
    Pushes an error using the current input stream position as input.

[Strategy::]push_error_up_to_here(|span| -> E) -> Strategy
    Pushes an error using the span from the start position to the current
    position as input.
    
    parser
        .to_recover()                       // define recovery strategy 
        .while_not(|| false,                // while not EOF:
            to_recover()                    //   define inner by means of a recovery strategy
            .push_error_up_to_here(         //   construct an error indicating which tokens
                |span| ignored_input(span)  //     were skipped
            ).retry()                       //   retry parsing from this point
            .or_fail()                      //   fail the inner strategy if that parser failed
        ).silently()                        // ignore errors from the inner recovery unless it succeeds
        .restart()...                       // if that failed, try something else

[Strategy::]push_error_for_next(|Option<&I>, span| -> E) -> Strategy
    Pushes an error for the next token.

[Strategy::]update_errors(|&mut Vec<E>|) -> Strategy
    Like push_error(), but given a mutable reference to the complete error list
    instead.

[Strategy::]update_errors_here(|&mut Vec<E>, location|) -> Strategy
    Like push_error_here(), but given a mutable reference to the complete error
    list instead.

[Strategy::]update_errors_up_to_here(|&mut Vec<E>, span|) -> Strategy
    Like push_error_up_to_here(), but given a mutable reference to the complete
    error list instead.

[Strategy::]update_errors_for_next(|&mut Vec<E>, Option<&I>, span|) -> Strategy
    Like push_error_for_next(), but given a mutable reference to the complete
    error list instead.

### Completing strategies

In order to complete a strategy and turn it into a parser again, you need to
use one of these.

Strategy::and_return(O) -> Parser
    Successfully completes a strategy by returning the given output, as if it
    had been parsed spanning from the start position to the current position.

Strategy::and_return_with(|| O) -> Parser
    Like and_return(), but uses a factory to construct the output.

Strategy::and_return_with_span(|span| O) -> Parser
    Like and_return(), but uses a factory to construct the output, which is
    also passed the span from the start position to the current position.

Strategy::or_fail() -> Parser
    Completes a strategy with failure if none of the preceding strategies
    were successful.

### Misc. strategies

Strategy::boxed() -> Strategy
    Boxes a strategy to fix its type.

Strategy::do_nothing() -> Strategy
    Just returns itself. Intended to be used with and_return() and friends for
    legibility when the recovery method is just to parse nothing and yield some
    output:
    
    parser.to_recover().do_nothing().and_return(output)

*/


use super::error;
use super::location;
use super::parser;
use super::stream;

/// Trait for recovery strategies.
pub trait Strategy<'i, I: 'i> {
    /// The parse tree type returned by the parser.
    type Output;

    /// The error type returned when parsing fails or recovery is required.
    type Error: error::Error<'i, I>;

    /// Called when the given parser has failed to parse starting from the
    /// current position in the given stream. The parser has successfully
    /// parsed up to `matched_up_to`, which can be passed to
    /// [stream::Stream::advance_to()] to seek to the location where the
    /// problems started. When recovery succeeds, the function must return
    /// Some with the recovered value and advance the stream accordingly;
    /// when it fails, it must return None and restore the stream state to
    /// what it was at the time of the call. In either case, the strategy
    /// may mutate `errors`; this is initialized with the list of errors
    /// originally returned by the parser, and used as the error list
    /// after the recovery call.
    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output>;

    /// Must call the parse_internal() method of the child parser, the
    /// parse_child() method of the child strategy, or return failure with
    /// no errors if neither is applicable. Simply used to traverse up into
    /// the combinator tree.
    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error>;

    /// Puts the strategy in a box to restrain it to a known type.
    fn boxed(self) -> Boxed<'i, I, Self::Output, Self::Error>
    where
        Self: Sized + 'i,
    {
        Boxed {
            child: Box::new(self),
        }
    }

    /// Seek to the token that caused the most-recently-called parser to fail,
    /// then fail recovery to hand control over to the next strategy.
    fn seek_to_failed(self) -> SeekToFailed<Self>
    where
        Self: Sized,
    {
        SeekToFailed { child: self }
    }

    /// Skip a single token, then fail recovery to hand control over to the
    /// next strategy. Does nothing if at EOF.
    fn skip(self) -> Skip<Self>
    where
        Self: Sized,
    {
        Skip { child: self }
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
        T: Scanner<'i, I, Self::Error>,
        F: Fn() -> T,
    {
        Scan {
            child: self,
            factory,
        }
    }

    /// While the token matcher function returns false, run the given strategy.
    /// Stop once the matcher returns true. This is like skip_until(), but with
    /// a strategy to run while skipping. Commonly used with [retry()].
    fn while_not<F, T>(self, predicate: F, inner: T) -> WhileNot<Self, F, T>
    where
        Self: Sized,
        F: Fn(&I) -> bool,
        T: Strategy<'i, I>,
    {
        WhileNot {
            child: self,
            predicate,
            inner,
        }
    }

    /// Try the given strategy. If this fails, continue from the current
    /// position, rather than from where the given strategy ended up. Errors
    /// are however maintained.
    fn maybe<T>(self, inner: T) -> Maybe<Self, T>
    where
        Self: Sized,
        T: Strategy<'i, I>,
    {
        Maybe { child: self, inner }
    }

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
    fn parse<T>(self, parser: T) -> Parse<Self, T>
    where
        Self: Sized,
        T: parser::Parser<'i, I, Output = Self::Output, Error = Self::Error>,
    {
        Parse {
            child: self,
            parser,
            exact: false,
            silent: false,
        }
    }

    /// Pushes an error at the current location.
    fn push_error_here<F>(self, factory: F) -> PushErrorHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            <<Self::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
        ) -> Self::Error,
    {
        PushErrorHere {
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
            <<Self::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ) -> Self::Error,
    {
        PushErrorForToken {
            child: self,
            factory,
        }
    }

    /// Updates the list of errors using the given function and the current
    /// location.
    fn update_errors_here<F>(self, updater: F) -> UpdateErrorsHere<Self, F>
    where
        Self: Sized,
        F: Fn(
            &mut Vec<Self::Error>,
            <<Self::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
        ),
    {
        UpdateErrorsHere {
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
            &mut Vec<Self::Error>,
            Option<&I>,
            <<Self::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ),
    {
        UpdateErrorsForToken {
            child: self,
            updater,
        }
    }

    /// Does nothing. You can use this when you want to recover by returning
    /// something without skipping any tokens and you want the functions to
    /// read like an English sentence; for example
    /// 
    /// ```
    /// parser.to_recover(attempt_to().do_nothing().and_return(...))
    /// ```
    fn do_nothing(self) -> Self
    where
        Self: Sized,
    {
        self
    }

    /// Succeed with recovery by emitting the given output, as if the tokens
    /// from the start position up to the current stream position had been
    /// parsed into that.
    fn and_return(self, output: Self::Output) -> Return<Self, Self::Output>
    where
        Self: Sized,
        Self::Output: Clone,
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
        F: Fn(
            <<Self::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
        ) -> Self::Output,
    {
        ReturnWith {
            child: self,
            output,
        }
    }

    // todo or_fail()
}

/// Helper function to implement [parser::Parser::parse_internal()] for
/// terminating strategies.
fn parse_internal_to_complete_strategy<'i, I, T>(
    strategy: &T,
    stream: &mut stream::Stream<'i, I, <<T as Strategy<'i, I>>::Error as error::Error<'i, I>>::LocationTracker>,
    enable_recovery: bool,
) -> parser::Result<<T as Strategy<'i, I>>::Output, <T as Strategy<'i, I>>::Error>
where
    I: 'i,
    T: Strategy<'i, I> + parser::Parser<'i, I, Output = <T as Strategy<'i, I>>::Output, Error = <T as Strategy<'i, I>>::Error>
{
    match strategy.parse_child(stream, enable_recovery) {
        parser::Result::Failed(last_token_matched, mut errors) => {
            if !enable_recovery {
                // Recovery disabled, don't run recovery strategy.
                parser::Result::Failed(last_token_matched, errors)
            } else {
                let started_at = stream.save();
                let mut failed_at = stream.save_at(last_token_matched);
                let recovery = strategy.recover(
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

/// See [parser::Parser::to_recover()] or [parser::Parser::to_recover()].
pub struct ToRecover<C> {
    pub(crate) child: C,
}

impl<'i, I, C> Strategy<'i, I> for ToRecover<C>
where
    I: 'i,
    C: parser::Parser<'i, I>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        _stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        _started_at: &stream::SavedState,
        _failed_at: &mut stream::SavedState,
        _errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        None
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_internal(stream, enable_recovery)
    }
}

/// See [Strategy::boxed()].
pub struct Boxed<'i, I, O, E> {
    pub(crate) child: Box<dyn Strategy<'i, I, Output = O, Error = E> + 'i>,
}

impl<'i, I, O, E> Strategy<'i, I> for Boxed<'i, I, O, E>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    type Output = O;
    type Error = E;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child.recover(stream, started_at, failed_at, errors)
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::seek_to_failed()].
pub struct SeekToFailed<C> {
    child: C,
}

impl<'i, I, C> Strategy<'i, I> for SeekToFailed<C>
where
    I: 'i,
    C: Strategy<'i, I>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.restore(failed_at);
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::skip()].
pub struct Skip<C> {
    child: C,
}

impl<'i, I, C> Strategy<'i, I> for Skip<C>
where
    I: 'i,
    C: Strategy<'i, I>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.advance();
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::find()].
pub struct Find<C, F> {
    child: C,
    predicate: F,
}

impl<'i, I, C, F> Strategy<'i, I> for Find<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(&I) -> bool,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                while !stream.token().map(&self.predicate).unwrap_or(true) {
                    stream.advance();
                }
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// Trait used to implement the [Strategy::scan()] recovery strategy.
pub trait Scanner<'i, I, E = error::Simple<'i, I>>
where
    I: 'i,
    E: error::Error<'i, I>,
{
    /// Called by [Strategy::scan()] recovery strategy for each token
    /// encountered on the input until this returns true. The given span is
    /// the span associated with the token. The given error list may be
    /// manipulated as needed.
    fn scan(
        &mut self,
        token: &'i I,
        span: <E::LocationTracker as location::Tracker<I>>::Span,
        errors: &mut Vec<E>,
    ) -> bool;

    /// Called by [Strategy::scan()] recovery strategy when EOF is
    /// encountered.
    fn eof(
        &mut self,
        _location: <E::LocationTracker as location::Tracker<I>>::Location,
        _errors: &mut Vec<E>,
    ) {
    }
}

/// See [nested_delimiters()].
pub struct NestedDelimiters<'i, I, C> {
    types: &'i [(I, I)],
    stack: Vec<(usize, &'i I, C)>,
}

impl<'i, I, C> NestedDelimiters<'i, I, C>
where
    I: PartialEq,
    C: Clone,
{
    fn handle_token<E, L>(&mut self, token: &'i I, span: C, errors: &mut Vec<E>)
    where
        E: error::Error<'i, I, LocationTracker = L>,
        L: location::Tracker<I, Span = C>,
    {
        // Try matching the right delimiter for the top of the stack first.
        // This handles the left = right delimiter case (like || for lambdas
        // in Rust, for example).
        if let Some((index, _, _)) = self.stack.last() {
            if token == &self.types[*index].1 {
                self.stack.pop();
                return;
            }
        }

        // See if this is a left delimiter.
        for (index, (left, _)) in self.types.iter().enumerate() {
            if token == left {
                self.stack.push((index, token, span));
                return;
            }
        }

        // See if this is a right delimiter. We already checked whether we
        // have the *correct* right delimiter, so if this matches something is
        // wrong.
        for (right_index, (_, right)) in self.types.iter().enumerate() {
            if token == right {
                // Now we have a decision problem. We can
                //  1) if there is a delimiter on our stack, treat this right
                //     delimiter as an incorrect delimiter for that one (pop
                //     stack);
                //  2) assume this is a right delimiter for something that was
                //     never opened (do nothing); or
                //  3) if there is a matching left delimiter elsewhere on our
                //     stack, assume the inner left delimiters were never
                //     closed (pop the stack multiple times).
                // All are pretty much equally valid. However, we'll solve by
                // scanning as lazily as possible, because this has the
                // greatest chance for the delimiter matcher to not gobble up
                // the entire input, and thus favors error verbosity and
                // recovering as much of the tree as possible. That means
                // option 3 if it applies, then option 1 if it applies, and
                // finally option 2.

                // Try option 3.
                if self
                    .stack
                    .iter()
                    .any(|(left_index, _, _)| *left_index == right_index)
                {
                    while let Some((left_index, left_token, left_span)) = self.stack.pop() {
                        if left_index == right_index {
                            // Popped the matching left delimiter.
                            return;
                        }

                        // Report unmatched left delimiter.
                        errors.push(E::unmatched_left_delimiter(
                            left_token,
                            left_span,
                            error::At::Span(span.clone()),
                        ));
                    }
                }

                // Try option 1.
                if let Some((left_index, left_token, left_span)) = self.stack.pop() {
                    assert!(left_index != right_index);

                    // Report incorrect delimiter.
                    errors.push(E::unmatched_delimiter_type(
                        left_token, left_span, token, span,
                    ));
                    return;
                }

                // Report unmatched right delimiter.
                errors.push(E::unmatched_right_delimiter(token, span, error::At::None));
                return;
            }
        }

        // If we get here, we scanned a token that does not participate in
        // delimiter matching, so we don't have to do anything.
    }
}

impl<'i, I, E> Scanner<'i, I, E>
    for NestedDelimiters<'i, I, <E::LocationTracker as location::Tracker<I>>::Span>
where
    I: PartialEq,
    E: error::Error<'i, I>,
    <E::LocationTracker as location::Tracker<I>>::Location: Clone,
    <E::LocationTracker as location::Tracker<I>>::Span: Clone,
{
    fn scan(
        &mut self,
        token: &'i I,
        span: <E::LocationTracker as location::Tracker<I>>::Span,
        errors: &mut Vec<E>,
    ) -> bool {
        self.handle_token(token, span, errors);
        self.stack.is_empty()
    }

    fn eof(
        &mut self,
        location: <E::LocationTracker as location::Tracker<I>>::Location,
        errors: &mut Vec<E>,
    ) {
        // Report unmatched left delimiters.
        while let Some((_, left_token, left_span)) = self.stack.pop() {
            errors.push(E::unmatched_left_delimiter(
                left_token,
                left_span,
                error::At::Location(location.clone()),
            ));
        }
    }
}

/// Scanner (see [Strategy::scan()]) for delimiter matching. This assumes that
/// the first token is the left delimiter for one of the provided types, and
/// then finds the matching right delimiter, leaving the parser state just
/// *before* it. Any unmatched delimiters encountered the process yield
/// suitable errors. If the first token is not a left delimiter, the parser
/// state is left unchanged and no errors will be generated. You may want to
/// prefix this with [Strategy::find()] to find the expected left delimiter
/// first, and suffix this with [Strategy::skip()] to skip past the right
/// delimiter.
pub fn nested_delimiters<'i, I, E>(types: &'i [(I, I)]) -> impl Fn() -> NestedDelimiters<'i, I, E>
where
    I: PartialEq,
    E: error::Error<'i, I>,
    <E::LocationTracker as location::Tracker<I>>::Location: Clone,
    <E::LocationTracker as location::Tracker<I>>::Span: Clone,
{
    || NestedDelimiters {
        types,
        stack: vec![],
    }
}

/// See [Strategy::scan()].
pub struct Scan<C, F> {
    child: C,
    factory: F,
}

impl<'i, I, C, F, T> Strategy<'i, I> for Scan<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn() -> T,
    T: Scanner<'i, I, C::Error>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
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

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::while_not()].
pub struct WhileNot<C, F, T> {
    child: C,
    predicate: F,
    inner: T,
}

impl<'i, I, C, F, T> Strategy<'i, I> for WhileNot<C, F, T>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(&I) -> bool,
    T: Strategy<'i, I, Output = C::Output, Error = C::Error>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                while !stream.token().map(&self.predicate).unwrap_or(true) {
                    if let Some(result) = self
                        .inner
                        .recover(stream, started_at, failed_at, errors)
                    {
                        return Some(result);
                    }
                    stream.advance();
                }
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::maybe()].
pub struct Maybe<C, T> {
    child: C,
    inner: T,
}

impl<'i, I, C, T> Strategy<'i, I> for Maybe<C, T>
where
    I: 'i,
    C: Strategy<'i, I>,
    T: Strategy<'i, I, Output = C::Output, Error = C::Error>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                stream.attempt(|stream| {
                    match self
                        .inner
                        .recover(stream, started_at, failed_at, errors)
                    {
                        Some(o) => Ok(Some(o)),
                        None => Err(None),
                    }
                })
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::retry()].
pub struct Retry<C> {
    child: C,
    exact: bool,
    silent: bool,
}

impl<C> Retry<C> {
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

impl<'i, I, C> Strategy<'i, I> for Retry<C>
where
    I: 'i,
    C: Strategy<'i, I>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| match self.parse_child(stream, !self.exact) {
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

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::parse()].
pub struct Parse<C, T> {
    child: C,
    parser: T,
    exact: bool,
    silent: bool,
}

impl<C, T> Parse<C, T> {
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

impl<'i, I, C, T> Strategy<'i, I> for Parse<C, T>
where
    I: 'i,
    C: Strategy<'i, I>,
    T: parser::Parser<'i, I, Output = C::Output, Error = C::Error>,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
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

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::push_error_here()].
pub struct PushErrorHere<C, F> {
    child: C,
    factory: F,
}

impl<'i, I, C, F> Strategy<'i, I> for PushErrorHere<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ) -> C::Error,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)(stream.location()));
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::push_error_for_token()].
pub struct PushErrorForToken<C, F> {
    child: C,
    factory: F,
}

impl<'i, I, C, F> Strategy<'i, I> for PushErrorForToken<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                errors.push((self.factory)(stream.token(), stream.span()));
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::update_errors_here()].
pub struct UpdateErrorsHere<C, F> {
    child: C,
    updater: F,
}

impl<'i, I, C, F> Strategy<'i, I> for UpdateErrorsHere<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(
        &mut Vec<C::Error>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Location,
    ) -> C::Error,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors, stream.location());
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::update_errors_for_token()].
pub struct UpdateErrorsForToken<C, F> {
    child: C,
    updater: F,
}

impl<'i, I, C, F> Strategy<'i, I> for UpdateErrorsForToken<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(
        &mut Vec<C::Error>,
        Option<&I>,
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Error,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| {
                (self.updater)(errors, stream.token(), stream.span());
                None
            })
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::and_return()].
pub struct Return<C, O> {
    child: C,
    output: O,
}

impl<'i, I, C> Strategy<'i, I> for Return<C, C::Output>
where
    I: 'i,
    C: Strategy<'i, I>,
    C::Output: Clone,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
           .or_else(|| Some(self.output.clone()))
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

/// See [Strategy::and_return_with()].
pub struct ReturnWith<C, F> {
    child: C,
    output: F,
}

impl<'i, I, C, F> Strategy<'i, I> for ReturnWith<C, F>
where
    I: 'i,
    C: Strategy<'i, I>,
    F: Fn(
        <<C::Error as error::Error<'i, I>>::LocationTracker as location::Tracker<I>>::Span,
    ) -> C::Output,
{
    type Output = C::Output;
    type Error = C::Error;

    fn recover(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        started_at: &stream::SavedState,
        failed_at: &mut stream::SavedState,
        errors: &mut Vec<Self::Error>,
    ) -> Option<Self::Output> {
        self.child
            .recover(stream, started_at, failed_at, errors)
            .or_else(|| Some((self.output)(stream.spanning_back_to(started_at))))
    }

    fn parse_child(
        &self,
        stream: &mut stream::Stream<'i, I, <Self::Error as error::Error<'i, I>>::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, Self::Error> {
        self.child.parse_child(stream, enable_recovery)
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn test_null_recovery() {
        let parser = just(&'a').with_error::<SimpleError<_>>()
            .to_recover().do_nothing().and_return(&'a');
            /*.with_error::<SimpleError<_>>();
        let mut stream = parser.stream(&['a', 'b', 'c']);
        assert_eq!(stream.next(), Some(ParseResult::Success(&'a')));
        assert_eq!(stream.tail().cloned().collect::<Vec<_>>(), vec!['b', 'c']);*/
    }
}