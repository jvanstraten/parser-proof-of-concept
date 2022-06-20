// SPDX-License-Identifier: Apache-2.0

use std::borrow::Borrow;

use super::error;
use super::location;

/// Trait used to implement the [Strategy::scan()] recovery strategy.
pub trait Scanner<'i, H, I, E = error::Simple<H, I>>
where
    H: Borrow<I> + Clone + 'i,
    I: 'i,
    E: error::Error<'i, H, I>,
{
    /// Called by [Strategy::scan()] recovery strategy for each token
    /// encountered on the input until this returns true. The given span is
    /// the span associated with the token. The given error list may be
    /// manipulated as needed.
    fn scan(
        &mut self,
        token: H,
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
pub struct NestedDelimiters<'i, H, I, S> {
    types: &'i [(H, H)],
    stack: Vec<(usize, H, S)>,
    phantom: std::marker::PhantomData<I>,
}

impl<'i, H, I, S> NestedDelimiters<'i, H, I, S>
where
    H: Borrow<I> + Clone + 'i,
    I: PartialEq + 'i,
    S: Clone,
{
    fn handle_token<E, L>(&mut self, token: H, span: S, errors: &mut Vec<E>)
    where
        E: error::Error<'i, H, I, LocationTracker = L>,
        L: location::Tracker<I, Span = S>,
    {
        // Try matching the right delimiter for the top of the stack first.
        // This handles the left = right delimiter case (like || for lambdas
        // in Rust, for example).
        if let Some((index, _, _)) = self.stack.last() {
            if token.borrow() == self.types[*index].1.borrow() {
                self.stack.pop();
                return;
            }
        }

        // See if this is a left delimiter.
        for (index, (left, _)) in self.types.iter().enumerate() {
            if token.borrow() == left.borrow() {
                self.stack.push((index, token, span));
                return;
            }
        }

        // See if this is a right delimiter. We already checked whether we
        // have the *correct* right delimiter, so if this matches something is
        // wrong.
        for (right_index, (_, right)) in self.types.iter().enumerate() {
            if token.borrow() == right.borrow() {
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

impl<'i, H, I, E> Scanner<'i, H, I, E>
    for NestedDelimiters<'i, H, I, <E::LocationTracker as location::Tracker<I>>::Span>
where
    H: Borrow<I> + Clone + 'i,
    I: PartialEq,
    E: error::Error<'i, H, I>,
    <E::LocationTracker as location::Tracker<I>>::Location: Clone,
    <E::LocationTracker as location::Tracker<I>>::Span: Clone,
{
    fn scan(
        &mut self,
        token: H,
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
pub fn nested_delimiters<'i, H, I, S>(
    types: &'i [(H, H)],
) -> impl Fn() -> NestedDelimiters<'i, H, I, S>
where
    I: PartialEq,
{
    || NestedDelimiters {
        types,
        stack: vec![],
        phantom: Default::default(),
    }
}
