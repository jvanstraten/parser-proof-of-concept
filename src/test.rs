// SPDX-License-Identifier: Apache-2.0

use super::prelude::*;

mod types {

    /// Trait for things that have a span.
    pub trait Spanned {
        type Span;

        fn span(&self) -> &Self::Span;
    }

    //=============================================================================

    /// Trait for the types of tokens within a language.
    pub trait TokenType: Copy + Eq + std::hash::Hash + std::fmt::Debug + std::fmt::Display {
        /// Array-like type returned by all().
        type All: IntoIterator<Item = Self>;

        /// Returns an iterator that iterates over all tokens, in the order in
        /// which they should be matched by the tokenizer.
        fn all() -> Self::All;

        /// Returns the regex for this token type.
        fn regex(&self) -> &'static str;

        /// Returns the regex for matching whitespace between the real tokens.
        fn whitespace() -> &'static str;
    }

    //=============================================================================

    /// Token classification.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum TokenClass<T> {
        /// Used for normal tokens, that the parser should consume.
        Normal(T),

        /// Used for the whitespace between normal tokens.
        Whitespace,

        /// Used to recover from errors; matches any single character when nothing
        /// else matches.
        Error,
    }

    impl<T: TokenType> TokenClass<T> {
        /// Returns the embedded token type if there is one.
        fn token_type(&self) -> Option<T> {
            if let Self::Normal(token_type) = self {
                Some(*token_type)
            } else {
                None
            }
        }

        /// Returns whether this is an error token.
        fn is_error(&self) -> bool {
            matches!(self, Self::Error)
        }

        /// Returns whether this is a whitespace token.
        fn is_whitespace(&self) -> bool {
            matches!(self, Self::Whitespace)
        }
    }

    impl<T: TokenType> std::fmt::Display for TokenClass<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                TokenClass::Normal(token_type) => std::fmt::Display::fmt(token_type, f),
                TokenClass::Whitespace => write!(f, "whitespace"),
                TokenClass::Error => write!(f, "error"),
            }
        }
    }

    //=============================================================================

    /// Tokens as emitted by the tokenizer. This includes errors and whitespace
    /// in addition to regular terminals in the grammar.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub struct Token<'a, T, L>
    where
        L: crate::location::Tracker<str>,
    {
        class: TokenClass<T>,
        text: &'a str,
        span: L::Span,
    }

    impl<'a, T, L> Token<'a, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<str>,
    {
        /// Creates a new token.
        pub fn new(class: TokenClass<T>, text: &'a str, span: L::Span) -> Self {
            Self { class, text, span }
        }

        /// Converts self to a [TerminalToken] if it is a normal token. Otherwise
        /// returns Err(self).
        pub fn to_grammar_input(self) -> Result<TerminalToken<T, L::Span>, Self> {
            if let Some(token_type) = self.class.token_type() {
                Ok(TerminalToken::new(token_type, self.text, self.span))
            } else {
                Err(self)
            }
        }

        /// Converts self to a [TokenizerError] if it is an error marker. Otherwise
        /// returns Err(self).
        pub fn to_error(self) -> Result<TokenizerError<L::Span>, Self> {
            if self.class.is_error() {
                Ok(TokenizerError::new(
                    self.text.chars().next().unwrap_or('?'),
                    self.span,
                ))
            } else {
                Err(self)
            }
        }

        /// Returns the class of this token.
        pub fn class(&self) -> TokenClass<T> {
            self.class
        }

        /// Returns the text encompassed by the token.
        pub fn text(&self) -> &'a str {
            self.text
        }
    }

    impl<'a, T, L> std::fmt::Display for Token<'a, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<str>,
        L::Span: std::fmt::Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{} ({:?} at {})", self.class, self.text, self.span)
        }
    }

    impl<'a, T, L> Spanned for Token<'a, T, L>
    where
        L: crate::location::Tracker<str>,
    {
        type Span = L::Span;

        fn span(&self) -> &Self::Span {
            &self.span
        }
    }

    //=============================================================================

    /// Error type used for a failure to tokenize.
    #[derive(Clone, Debug)]
    pub struct TokenizerError<S> {
        invalid_char: char,
        location: S,
    }

    impl<S: std::fmt::Display> std::fmt::Display for TokenizerError<S> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "failed to match character {:?} as the start of a token at {}",
                self.invalid_char, self.location
            )
        }
    }

    impl<S> TokenizerError<S> {
        pub fn new(invalid_char: char, location: S) -> Self {
            Self {
                invalid_char,
                location,
            }
        }
    }

    //=============================================================================

    pub struct Tokenizer<'s, T, L = crate::location::Simple> {
        regexes: Vec<(regex::Regex, TokenClass<T>)>,
        location: L,
        index: usize,
        remain: &'s str,
    }

    impl<'s, T, L> Tokenizer<'s, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<str>,
    {
        /// Creates a tokenizer for a piece of text with the given initial location
        /// for spans.
        pub fn new_with_location(location: L, text: &'s str) -> Self {
            let mut regexes: Vec<_> = T::all()
                .into_iter()
                .map(|x| {
                    (
                        regex::Regex::new(&format!("^(?:{})", x.regex())).unwrap(),
                        TokenClass::Normal(x),
                    )
                })
                .collect();
            regexes.push((
                regex::Regex::new(&format!("^(?:{})", T::whitespace())).unwrap(),
                TokenClass::Whitespace,
            ));
            Self {
                regexes,
                location,
                index: 0,
                remain: text,
            }
        }

        /// Creates a tokenizer for a piece of text, using L::default() for the
        /// initial location.
        pub fn new(text: &'s str) -> Self
        where
            L: Default,
        {
            Self::new_with_location(L::default(), text)
        }
    }

    impl<'s, T, L> Iterator for Tokenizer<'s, T, L>
    where
        T: TokenType,
        L: crate::location::Tracker<str>,
    {
        type Item = Token<'s, T, L>;

        fn next(&mut self) -> Option<Self::Item> {
            // Stop when we reach EOF.
            if self.remain.is_empty() {
                return None;
            }

            // Look for the first longest match.
            let mut token_type = TokenClass::Error;
            let mut length = 0;
            for (regex, candidate_token_type) in self.regexes.iter() {
                let candidate_length = regex
                    .captures(self.remain)
                    .and_then(|x| x.get(0))
                    .map(|x| x.as_str().len())
                    .unwrap_or_default();
                if candidate_length > length {
                    token_type = *candidate_token_type;
                    length = candidate_length;
                }
            }

            // Advance by at least one character, even if nothing matched, in
            // an attempt to recover from errors.
            if length == 0 {
                length = 1;
            }

            // Generate the token and seek past it.
            let text = &self.remain[..length];
            self.remain = &self.remain[length..];
            let start_location = self.location.clone();
            let start_index = self.index;
            self.location.advance(&text);
            self.index += 1;
            let span = start_location.spanning_to(start_index, &self.location, self.index);
            let token = Token::new(token_type, text, span);

            Some(token)
        }
    }

    //=============================================================================

    /// Token type used as terminals at the input of the grammar. This type is a
    /// bit derpy to make Chumsky work right: two terminal tokens are equal iff
    /// they have the same type, with no bearing on the text or span. The text or
    /// span are treated as optional annotations, used only to aid in the
    /// construction of error messages.
    #[derive(Clone, Debug, Eq, Hash)]
    pub struct TerminalToken<T: TokenType, S> {
        token_type: T,
        text: Option<String>,
        span: S,
    }

    impl<T: TokenType, S> PartialEq for TerminalToken<T, S> {
        fn eq(&self, other: &Self) -> bool {
            self.token_type == other.token_type
        }
    }

    impl<T: TokenType, S> TerminalToken<T, S> {
        /// Creates a new terminal node.
        pub fn new<R: ToString>(token_type: T, text: R, span: S) -> Self {
            Self {
                token_type,
                text: Some(text.to_string()),
                span,
            }
        }

        /// Creates a new "pattern" node, only used for error messages and to
        /// compare against.
        pub fn new_pattern(token_type: T) -> Self
        where
            S: Default,
        {
            Self {
                token_type,
                text: None,
                span: S::default(),
            }
        }

        /// Returns the token type.
        pub fn token_type(&self) -> T {
            self.token_type
        }

        /// Returns the text enclosed by the token.
        pub fn text(&self) -> &str {
            self.text.as_ref().map(|x| &x[..]).unwrap_or("")
        }

        /// Unwraps the contents into a tuple.
        pub fn unwrap(self) -> (T, Option<String>, S) {
            (self.token_type, self.text, self.span)
        }
    }

    impl<T: TokenType, S: std::fmt::Display> std::fmt::Display for TerminalToken<T, S> {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            if let Some(text) = &self.text {
                write!(f, "{} ({:?}) at {}", self.token_type, text, self.span)
            } else {
                write!(f, "{}", self.token_type)
            }
        }
    }

    impl<T: TokenType, S> Spanned for TerminalToken<T, S> {
        type Span = S;

        fn span(&self) -> &S {
            &self.span
        }
    }

    //=============================================================================

    // Error type used for both parsing and tokenization.
    #[derive(Clone, Debug)]
    pub enum Error<'i, L>
    where
        L: crate::location::Tracker<str>,
        L::Location: Clone + std::fmt::Debug + std::fmt::Display,
        L::Span: Clone + std::fmt::Debug + std::fmt::Display,
    {
        TokenizerError(TokenizerError<L::Location>),
        ParserError(crate::error::Simple<&'i str, str, L>),
    }

    impl<'i, L> std::fmt::Display for Error<'i, L>
    where
        L: crate::location::Tracker<str>,
        L::Location: Clone + std::fmt::Debug + std::fmt::Display,
        L::Span: Clone + std::fmt::Debug + std::fmt::Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Error::TokenizerError(e) => write!(f, "{e}"),
                Error::ParserError(e) => write!(f, "{e}"),
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenType {
    /// Implicit token.
    Pls,

    Val,
}

impl types::TokenType for TokenType {
    type All = [TokenType; 2];

    fn all() -> Self::All {
        [Self::Pls, Self::Val]
    }

    fn regex(&self) -> &'static str {
        match self {
            Self::Pls => "\\+",
            Self::Val => "(?:[0-9])+",
        }
    }

    fn whitespace() -> &'static str {
        "(?:[ \\\\t\\\\r\\\\n])+"
    }
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Tokenizes a piece of text.
pub fn tokenize<'s>(text: &'s str) -> types::Tokenizer<'s, TokenType> {
    types::Tokenizer::new(text)
}

/// Tokenizes a piece of text starting from the given source location.
pub fn tokenize_from<'s, L: crate::location::Tracker<str>>(
    location: L,
    text: &'s str,
) -> types::Tokenizer<'s, TokenType, L> {
    types::Tokenizer::new_with_location(location, text)
}

/// Helper type for a boxed parser.
pub type BoxedParser<'i, T, S> = crate::combinator::Boxed<
    'i,
    &'i types::TerminalToken<TokenType, S>,
    &'i types::TerminalToken<TokenType, S>,
    T,
>;

/// Helper type for the contents of a token.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TokenData<'i, S> {
    pub token: &'i types::TerminalToken<TokenType, S>,
    pub index: usize,
}

/// Implicit token.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PtPls<'i, S> {
    pub data: Option<TokenData<'i, S>>,
}

impl<'i, S> PtPls<'i, S> {
    fn new(
        token: &'i types::TerminalToken<TokenType, S>,
        token_span: std::ops::Range<usize>,
    ) -> Self {
        assert!(token.token_type() == TokenType::Pls);
        Self {
            data: Some(TokenData {
                token,
                index: token_span.start,
            }),
        }
    }

    /// Visit this terminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Pls(self)
    }

    /// Visit this terminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Pls(self)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PtVal<'i, S> {
    pub data: Option<TokenData<'i, S>>,
}

impl<'i, S> PtVal<'i, S> {
    fn new(
        token: &'i types::TerminalToken<TokenType, S>,
        token_span: std::ops::Range<usize>,
    ) -> Self {
        assert!(token.token_type() == TokenType::Val);
        Self {
            data: Some(TokenData {
                token,
                index: token_span.start,
            }),
        }
    }

    /// Visit this terminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Val(self)
    }

    /// Visit this terminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Val(self)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PtGrammar<'i, S>(Box<PtSum<'i, S>>);

impl<'i, S: Default + Eq + std::hash::Hash> PtGrammar<'i, S> {
    /// Return a Chumsky parser for this rule.
    pub fn parser<'a>() -> BoxedParser<'a, PtGrammar<'i, S>, S> {
        make_parsers().0
    }

    /// Visit this nonterminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Grammar(self)
    }

    /// Visit this nonterminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Grammar(self)
    }

    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        let x1 = &self.0;
        visitor.visit_Sum(x1.as_ref())?;
        Ok(())
    }

    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        let x1 = &mut self.0;
        visitor.visit_Sum(x1.as_mut())?;
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PtSum<'i, S>(PtVal<'i, S>, PtPls<'i, S>, PtVal<'i, S>);

impl<'i, S: Default + Eq + std::hash::Hash> PtSum<'i, S> {
    /// Return a Chumsky parser for this rule.
    pub fn parser<'a>() -> BoxedParser<'a, PtSum<'i, S>, S> {
        make_parsers().1
    }

    /// Visit this nonterminal node with the given visitor.
    pub fn visit<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Sum(self)
    }

    /// Visit this nonterminal node with the given visitor.
    pub fn visit_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        visitor.visit_Sum(self)
    }

    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse<E, V: Visitor<'i, S, E>>(&self, visitor: &mut V) -> Result<(), E> {
        let x1 = &self.0;
        let x2 = &self.1;
        let x3 = &self.2;
        visitor.visit_Val(x1)?;
        visitor.visit_Pls(x2)?;
        visitor.visit_Val(x3)?;
        Ok(())
    }

    /// Visit the children of this nonterminal node with the given visitor.
    pub fn traverse_mut<E, V: VisitorMut<'i, S, E>>(&mut self, visitor: &mut V) -> Result<(), E> {
        let x1 = &mut self.0;
        let x2 = &mut self.1;
        let x3 = &mut self.2;
        visitor.visit_Val(x1)?;
        visitor.visit_Pls(x2)?;
        visitor.visit_Val(x3)?;
        Ok(())
    }
}

/// Constructs Chumsky parsers for all the grammar rules.
#[allow(non_snake_case)]
fn make_parsers<'a, 'i, S: Default + Eq + std::hash::Hash>() -> (
    BoxedParser<'a, PtGrammar<'i, S>, S>,
    BoxedParser<'a, PtSum<'i, S>, S>,
) {
    let mut parse_Grammar = Recursive::declare();
    let mut parse_Sum = Recursive::declare();

    parse_Grammar.define(
        parse_Sum
            .clone()
            .map(Box::new)
            .map(|x| PtGrammar(x))
            .boxed(),
    );

    parse_Sum.define(
        one_of::<_, _, &'i types::TerminalToken<TokenType, S>, _>(&[
            types::TerminalToken::new_pattern(TokenType::Val),
        ])
        .map_with_span(PtVal::new)
        .boxed()
        .then(
            one_of::<_, _, &'i types::TerminalToken<TokenType, S>, _>(&[
                types::TerminalToken::new_pattern(TokenType::Pls),
            ])
            .map_with_span(PtPls::new)
            .boxed(),
        )
        .then(
            one_of::<_, _, &'i types::TerminalToken<TokenType, S>, _>(&[
                types::TerminalToken::new_pattern(TokenType::Val),
            ])
            .map_with_span(PtVal::new)
            .boxed(),
        )
        .map(|((x1, x2), x3)| (x1, x2, x3))
        .boxed()
        .map(|(x1, x2, x3)| PtSum(x1, x2, x3))
        .boxed(),
    );

    (
        parse_Grammar.then_ignore(end()).boxed(),
        parse_Sum.then_ignore(end()).boxed(),
    )
}

/// Visitor trait for immutably walking the parse tree.
pub trait Visitor<'i, S, E = ()>
where
    Self: Sized,
{
    #[allow(non_snake_case)]
    fn visit_Pls(&mut self, _x: &PtPls<'i, S>) -> Result<(), E> {
        Ok(())
    }

    #[allow(non_snake_case)]
    fn visit_Val(&mut self, _x: &PtVal<'i, S>) -> Result<(), E> {
        Ok(())
    }

    #[allow(non_snake_case)]
    fn visit_Grammar(&mut self, x: &PtGrammar<'i, S>) -> Result<(), E> {
        x.traverse(self)
    }

    #[allow(non_snake_case)]
    fn visit_Sum(&mut self, x: &PtSum<'i, S>) -> Result<(), E> {
        x.traverse(self)
    }
}

/// Visitor trait for mutably walking the parse tree.
pub trait VisitorMut<'i, S, E = ()>
where
    Self: Sized,
{
    #[allow(non_snake_case)]
    fn visit_Pls(&mut self, _x: &mut PtPls<'i, S>) -> Result<(), E> {
        Ok(())
    }

    #[allow(non_snake_case)]
    fn visit_Val(&mut self, _x: &mut PtVal<'i, S>) -> Result<(), E> {
        Ok(())
    }

    #[allow(non_snake_case)]
    fn visit_Grammar(&mut self, x: &mut PtGrammar<'i, S>) -> Result<(), E> {
        x.traverse_mut(self)
    }

    #[allow(non_snake_case)]
    fn visit_Sum(&mut self, x: &mut PtSum<'i, S>) -> Result<(), E> {
        x.traverse_mut(self)
    }
}
