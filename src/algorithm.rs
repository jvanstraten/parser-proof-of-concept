// SPDX-License-Identifier: Apache-2.0

use super::combinator;
use super::error;
use super::location;
use super::parser;

// Concatenate a set of parsers that is completely known at compile time into
// a tuple.
macro_rules! concatenate {
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
                crate::parser::Result::Success(a) => a,
                crate::parser::Result::Recovered(a, es_a) => {
                    recovery = Some(es_a);
                    a
                }
                crate::parser::Result::Failed(i, es) => {
                    // No need to restore state, because the only parser we ran
                    // failed.
                    return crate::parser::Result::Failed(i, es);
                }
            },

            $(
                // Parse the other children.
                match $other.parse_internal($stream, $enable_recovery) {
                    crate::parser::Result::Success(b) => b,
                    crate::parser::Result::Recovered(b, es_b) => {
                        if let Some(es) = &mut recovery {
                            es.extend(es_b);
                        } else {
                            recovery = Some(es_b);
                        }
                        b
                    }
                    crate::parser::Result::Failed(i, es) => {
                        // Need to restore the state here, previous parsers
                        // will have mutated it.
                        $stream.restore(&initial);
                        return crate::parser::Result::Failed(i, es);
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
            crate::parser::Result::Recovered(o, es)
        } else {
            crate::parser::Result::Success(o)
        }
    }};
}

// Concatenate a set of boxed parsers that all return the same type into
// a vector.
pub fn concatenate<'i, 'p, I, O, L, E, P>(
    stream: &mut crate::stream::Stream<'i, I, L>,
    enable_recovery: bool,
    parsers: P,
) -> parser::Result<Vec<O>, E>
where
    'i: 'p,
    I: 'i,
    O: 'i,
    L: location::LocationTracker<I> + 'p,
    E: error::Error<'i, I, L> + 'p,
    P: IntoIterator<Item = &'p combinator::Boxed<'i, I, O, L, E>>,
{
    let mut parsers = parsers.into_iter();

    // Store the initial state, which we'll need to restore if the first
    // parser succeeds but the second fails.
    let initial = stream.save();

    // Set to Some(errors) when a child parser recovered from a parse
    // error.
    let mut recovery = None;

    // Gather the results in a vector.
    let mut output = Vec::with_capacity(parsers.size_hint().0);

    // Parse the first child.
    if let Some(parser) = parsers.next() {
        output.push(
            match parser::Parser::parse_internal(parser, stream, enable_recovery) {
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
        );
    }

    // Parse the other children.
    for parser in parsers {
        output.push(
            match parser::Parser::parse_internal(parser, stream, enable_recovery) {
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
                    stream.restore(&initial);
                    return parser::Result::Failed(i, es);
                }
            },
        );
    }

    // Return success or recovered based on whether any of the parsers
    // resovered.
    if let Some(es) = recovery {
        assert!(enable_recovery);
        parser::Result::Recovered(output, es)
    } else {
        parser::Result::Success(output)
    }
}

// Parse using the same parser a configurable number of times.
#[allow(clippy::too_many_arguments)] // no u
pub fn repeat<'i, 'p, I, L, E, P, S>(
    stream: &mut crate::stream::Stream<'i, I, L>,
    enable_recovery: bool,
    minimum: usize,
    maximum: Option<usize>,
    parser: &'p P,
    separator: Option<&'p S>,
    allow_leading: bool,
    allow_trailing: bool,
) -> parser::Result<Vec<P::Output>, E>
where
    'i: 'p,
    I: 'i,
    L: location::LocationTracker<I> + 'p,
    E: error::Error<'i, I, L> + 'p,
    P: parser::Parser<'i, I, L, E>,
    S: parser::Parser<'i, I, L, E>,
{
    let max = maximum.unwrap_or(usize::MAX);

    // Store the initial state, which we'll need to restore if the first
    // parser succeeds but the second fails.
    let initial = stream.save();

    // Set to Some(errors) when a child parser recovered from a parse
    // error.
    let mut recovery: Option<Vec<E>> = None;

    // Gather the results in a vector.
    let mut output = Vec::with_capacity(minimum);

    // Parse items.
    loop {
        // If we don't allow trailing separators, stop parsing here if we have
        // the maximum amount of items already.
        if !allow_trailing && output.len() >= max {
            break;
        }

        // Enable recovery only if we don't have the minimum amount of items
        // yet. After that, failure to parse just means there are no more
        // items on the input.
        let recover = enable_recovery && output.len() < minimum;

        // Match the separator. Store the parser state before the separator
        // if a separator is enabled, so we can backtrack to that point if
        // parsing the separator succeeds but parsing the item fails. If
        // trailing separators are allowed we also save the state because this
        // is complicated enough as is, but we don't restore it in that case.
        let before_separator =
            if let (Some(separator), true) = (separator, !output.is_empty() || allow_leading) {
                let before_separator = stream.save();
                match parser::Parser::parse_internal(separator, stream, recover) {
                    parser::Result::Success(_) => (),
                    parser::Result::Recovered(_, es_b) => {
                        if let Some(es) = &mut recovery {
                            es.extend(es_b);
                        } else {
                            recovery = Some(es_b);
                        }
                    }
                    parser::Result::Failed(i, es) => {
                        if output.len() >= minimum {
                            // We've already matched enough, we're done.
                            return parser::Result::Success(output);
                        } else {
                            // We've not matched the minimum amount of repetitions
                            // yet. Getting here also means recovery failed. We
                            // need to restore the state here; previous parsers
                            // will have mutated it.
                            stream.restore(&initial);
                            return parser::Result::Failed(i, es);
                        }
                    }
                }
                Some(before_separator)
            } else {
                None
            };

        // If we do allow for trailing separators, stop parsing here if we have
        // the maximum amount of items.
        if allow_trailing && output.len() >= max {
            break;
        }

        // Match the next item.
        output.push(
            match parser::Parser::parse_internal(parser, stream, recover) {
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
                    if output.len() >= minimum {
                        // We've already matched enough, we're done. We may
                        // however need to restore the state to before the
                        // separator, which already matched if there was one.
                        if let Some(state) = before_separator {
                            if !allow_trailing {
                                stream.restore(&state);
                            }
                        }
                        return parser::Result::Success(output);
                    } else {
                        // We've not matched the minimum amount of repetitions
                        // yet. Getting here also means recovery failed. We
                        // need to restore the state here; previous parsers
                        // will have mutated it.
                        stream.restore(&initial);
                        return parser::Result::Failed(i, es);
                    }
                }
            },
        );
    }

    // Return success or recovered based on whether any of the parsers
    // resovered.
    if let Some(es) = recovery {
        assert!(enable_recovery);
        parser::Result::Recovered(output, es)
    } else {
        parser::Result::Success(output)
    }
}

macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + count!($($xs)*));
}

macro_rules! get {
    (@step $idx_var:expr, $_idx:expr,) => {
        panic!("get!() index out of range")
    };

    (@step $idx_var:expr, $idx:expr, $head:expr, $($tail:expr,)*) => {
        if $idx_var == $idx {
            $head
        } else {
            get!(@step $idx_var, $idx + 1usize, $($tail,)*)
        }
    };

    ($i:expr, $($x:expr),*) => {
        get!(@step $i, 0usize, $($x,)*)
    }
}

// Alternate between a set of parsers that is completely known at compile time.
macro_rules! alternate {
    ($stream:expr, $enable_recovery:expr, $($parsers:expr),+) => {{
        let stream = $stream;

        // Try all alternatives without enabling recovery, returning the first that
        // matches. Record the failures in case none of the parsers match.
        let mut failures = Vec::with_capacity(count!($($parsers)+));
        $(
            match crate::parser::Parser::parse_internal($parsers, stream, false) {
                crate::parser::Result::Success(o) => return parser::Result::Success(o),
                crate::parser::Result::Recovered(_, _) => unreachable!("parser recovered from an error with recovery disabled"),
                crate::parser::Result::Failed(i, es) => failures.push((i, es, failures.len())),
            }
        )+

        // Order the parsers by descending index of the last token matched. We'll
        // try to recover in this order; the option with the most tokens matched
        // is the one that the user is the most likely to have intended.
        failures.sort_by_key(|x| std::cmp::Reverse(x.0));

        // If recovery is enabled, try to recover in the above sort order.
        if $enable_recovery {
            for (_, _, parser_index) in &failures {
                match get!(
                    *parser_index,
                    $(parser::Parser::parse_internal($parsers, stream, true)),+
                ) {
                    parser::Result::Success(_) => unreachable!("parser that previously failed now magically succeeded"),
                    parser::Result::Recovered(o, es) => return parser::Result::Recovered(o, es),
                    parser::Result::Failed(_, _) => (),
                }
            }
        }

        // Try to combine error messages intelligently. If the most likely
        // alternative only returned a single expected-found error, merge the
        // errors from the other types into it; if it did something smarter
        // than that, don't argue with it and just return those errors as-is.
        let mut failures = failures.into_iter();
        let (last_token_matched, es, _) = failures.next().unwrap();
        if es.len() == 1 && es[0].is_expected_found() {
            let mut e = es.into_iter().next().unwrap();
            for (_, es2, _) in failures {
                for e2 in es2 {
                    if e2.is_expected_found() && e2.location() == e.location() {
                        e.merge_expected_found(&e2);
                    }
                }
            }
            parser::Result::Failed(last_token_matched, vec![e])
        } else {
            let (last_token_matched, es, _) = failures.into_iter().next().unwrap();
            parser::Result::Failed(last_token_matched, es)
        }
    }};
}

// Alternate between a set of boxed parsers (at least one) that all return the
// same type.
pub fn alternate<'i, 'p, I, O, L, E, P>(
    stream: &mut crate::stream::Stream<'i, I, L>,
    enable_recovery: bool,
    parsers: P,
) -> parser::Result<O, E>
where
    'i: 'p,
    I: 'i,
    O: 'i,
    L: location::LocationTracker<I> + 'p,
    E: error::Error<'i, I, L> + 'p,
    P: IntoIterator<Item = &'p combinator::Boxed<'i, I, O, L, E>>,
{
    let parsers = parsers.into_iter();

    // Try all alternatives without enabling recovery, returning the first that
    // matches. Record the failures in case none of the parsers match.
    let mut failures = Vec::with_capacity(parsers.size_hint().0);
    for parser in parsers {
        match parser::Parser::parse_internal(parser, stream, false) {
            parser::Result::Success(o) => return parser::Result::Success(o),
            parser::Result::Recovered(_, _) => {
                unreachable!("parser recovered from an error with recovery disabled")
            }
            parser::Result::Failed(i, es) => failures.push((i, es, parser)),
        }
    }

    assert!(
        !failures.is_empty(),
        "cannot have zero alternatives for alternate()"
    );

    // Order the parsers by descending index of the last token matched. We'll
    // try to recover in this order; the option with the most tokens matched
    // is the one that the user is the most likely to have intended.
    failures.sort_by_key(|x| std::cmp::Reverse(x.0));

    // If recovery is enabled, try to recover in the above sort order.
    if enable_recovery {
        for (_, _, parser) in &failures {
            match parser::Parser::parse_internal(*parser, stream, true) {
                parser::Result::Success(_) => {
                    unreachable!("parser that previously failed now magically succeeded")
                }
                parser::Result::Recovered(o, es) => return parser::Result::Recovered(o, es),
                parser::Result::Failed(_, _) => (),
            }
        }
    }

    // Try to combine error messages intelligently. If the most likely
    // alternative only returned a single expected-found error, merge the
    // errors from the other types into it; if it did something smarter
    // than that, don't argue with it and just return those errors as-is.
    let mut failures = failures.into_iter();
    let (last_token_matched, es, _) = failures.next().unwrap();
    if es.len() == 1 && es[0].is_expected_found() {
        let mut e = es.into_iter().next().unwrap();
        for (_, es2, _) in failures {
            for e2 in es2 {
                if e2.is_expected_found() && e2.location() == e.location() {
                    e.merge_expected_found(&e2);
                }
            }
        }
        parser::Result::Failed(last_token_matched, vec![e])
    } else {
        let (last_token_matched, es, _) = failures.into_iter().next().unwrap();
        parser::Result::Failed(last_token_matched, es)
    }
}
