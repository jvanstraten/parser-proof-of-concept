// SPDX-License-Identifier: Apache-2.0

use crate::prelude::*;

#[derive(Clone, Debug)]
enum Value {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    String(String),
    Object(Vec<(String, Value)>),
    Array(Vec<Value>),
}

type ErrorType<I> = VoidedError<I>;

#[test]
fn test_json() {
    // Define a JSON parser.
    let json = recursive(|value| {
        // Whitespace parsing.
        let whitespace = one_of(" \n\r\t").repeated();

        // Keyword parsing.
        let null = seq("null").to(Value::Null);
        let bool_true = seq("true").to(Value::Bool(true));
        let bool_false = seq("false").to(Value::Bool(false));

        // String parsing.
        let hex_to_u32 = |c: &char| {
            // why does char::to_digit() have to be unstable? lame...
            match *c {
                '0'..='9' => Some((*c as u32) - ('o' as u32)),
                'a'..='f' => Some((*c as u32) - ('a' as u32) + 10),
                'A'..='F' => Some((*c as u32) - ('A' as u32) + 10),
                _ => None,
            }
        };

        let collapse_hex = |(msb, lsb)| msb * 16 + lsb;

        let hex_escape = filter_map(hex_to_u32)
            .then(filter_map(hex_to_u32))
            .map(collapse_hex)
            .then(filter_map(hex_to_u32))
            .map(collapse_hex)
            .then(filter_map(hex_to_u32))
            .map(collapse_hex)
            .try_map(|code_point, span| match char::from_u32(code_point) {
                Some(c) => TryMapResult::Ok(c),
                None => TryMapResult::Recovered(
                    '?',
                    vec![ErrorType::custom(
                        format!("illegal code point: \\x{code_point:04x}"),
                        At::Span(span),
                    )],
                ),
            })
            .boxed();

        let escape = just('"')
            .alters(just('\\'))
            .and(just('/'))
            .and(just('b').to('\x08'))
            .and(just('f').to('\x0C'))
            .and(just('n').to('\n'))
            .and(just('r').to('\r'))
            .and(just('t').to('\t'))
            .and(just('u').ignore_then(hex_escape))
            .boxed();

        let key = none_of("\"\\")
            .or(just('\\').ignore_then(escape))
            .repeated()
            .delimited_by(just('"'), just('"'))
            .map(|x| x.into_iter().collect::<String>())
            .boxed();

        let string = key.clone().map(Value::String).boxed();

        // Number parsing.
        let sign = just('-').or_not().map(|x| x.is_some()).boxed();

        let integer_nlz = just('0')
            .to(String::from("0"))
            .or(one_of("123456789")
                .then(one_of("0123456789").repeated())
                .map(|(msb, lsbs)| {
                    let mut s = String::from(msb);
                    s.extend(lsbs);
                    s
                }))
            .boxed();

        let integer_lz = one_of("0123456789")
            .repeated()
            .at_least(1)
            .map(|x| x.into_iter().collect::<String>())
            .boxed();

        let fraction = just('.').ignore_then(integer_lz.clone()).boxed();

        let exponent_sign = one_of("-+")
            .or_not()
            .map(|x| match x {
                Some('-') => true,
                _ => false,
            })
            .boxed();

        let exponent = one_of("eE")
            .ignore_then(exponent_sign)
            .then(integer_lz)
            .boxed();

        let number = sign
            .then(integer_nlz)
            .then(fraction.or_not())
            .then(exponent.or_not())
            .try_map(|(((sign, int), frac), exp), span| {
                if frac.is_some() || exp.is_some() {
                    let mut number = String::new();
                    if sign {
                        number.push('-');
                    }
                    number += &int;
                    if let Some(frac) = frac {
                        number.push('.');
                        number += &frac;
                    }
                    if let Some((sign, exp)) = exp {
                        number.push('e');
                        if sign {
                            number.push('-');
                        }
                        number += &exp;
                    }
                    if let Ok(parsed) = int.parse::<f64>() {
                        TryMapResult::Ok(Value::Float(parsed))
                    } else {
                        TryMapResult::Recovered(
                            Value::Int(0),
                            vec![ErrorType::custom(
                                format!("float parse error"),
                                At::Span(span),
                            )],
                        )
                    }
                } else {
                    if let Ok(parsed) = int.parse::<i128>() {
                        TryMapResult::Ok(Value::Int(if sign { -parsed } else { parsed }))
                    } else {
                        TryMapResult::Recovered(
                            Value::Int(0),
                            vec![ErrorType::custom(
                                format!("integer too large"),
                                At::Span(span),
                            )],
                        )
                    }
                }
            })
            .boxed();

        // Nested parsing.
        let key_value_pair = whitespace
            .clone()
            .ignore_then(key)
            .then_ignore(whitespace.clone())
            .then_ignore(just(':'))
            .then(value.clone())
            .boxed();

        let object = key_value_pair
            .separated_by(just(','))
            .or(whitespace.clone().to(vec![]))
            .delimited_by(just('{'), just('}'))
            .map(Value::Object)
            .boxed();

        let array = value
            .clone()
            .separated_by(just(','))
            .or(whitespace.clone().to(vec![]))
            .delimited_by(just('['), just(']'))
            .map(Value::Array)
            .boxed();

        // Value parsing.
        object
            .alters(array)
            .and(string)
            .and(bool_true)
            .and(bool_false)
            .and(null)
            .and(number)
            .padded_by(whitespace)
            .with_error::<ErrorType<char>>()
    });

    let input = include_str!("sample.json");
    let iterator = std::iter::repeat(input).map(|x| x.chars()).flatten();

    let started_at = std::time::Instant::now();
    let duration = std::time::Duration::new(3, 0);
    let stop_at = started_at + duration;

    let mut count = 0;
    for result in json.stream(iterator) {
        count += 1;
        assert_eq!(result.errors().next(), None);
        let now = std::time::Instant::now();
        if std::time::Instant::now() > stop_at {
            println!(
                "{} characters parsed in {:?}",
                count * input.len(),
                now - started_at
            );
            println!(
                "{}ns per iteration",
                (now - started_at).as_nanos() / (count as u128)
            );
            break;
        }
    }
}
