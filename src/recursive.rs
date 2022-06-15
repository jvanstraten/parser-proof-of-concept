use super::combinator;
use super::error;
use super::location;
use super::parser;
use std::cell::RefCell;
use std::rc::Rc;

pub struct Recursive<'i, I, O, L, E> {
    #[allow(clippy::type_complexity)]
    inner: Rc<RefCell<Option<combinator::Boxed<'i, I, O, L, E>>>>,
}

impl<'i, I, O, L, E> Recursive<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    /// Declare the existence of a recursive parser, allowing it to be used
    /// to construct parser combinators before being fulled defined.
    pub fn declare() -> Self {
        Self {
            inner: Default::default(),
        }
    }

    /// Defines the parser after declaring it, allowing it to be used for
    /// parsing.
    pub fn define<P>(&mut self, parser: P)
    where
        P: parser::Parser<'i, I, L, E, Output = O> + 'i,
    {
        assert!(
            self.inner.borrow_mut().replace(parser.boxed()).is_none(),
            "multiple definitions for recursive parser"
        );
    }
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for Recursive<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = O;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.inner
            .borrow()
            .as_ref()
            .expect("recursive parser is not defined")
            .parse_internal(stream, enable_recovery)
    }
}

pub fn recursive<'i, I, O, L, E, P, F>(f: F) -> Recursive<'i, I, O, L, E>
where
    I: 'i,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
    P: parser::Parser<'i, I, L, E, Output = O> + 'i,
    F: FnOnce(&Recursive<'i, I, O, L, E>) -> P,
{
    let mut recursive = Recursive::declare();
    recursive.define(f(&recursive));
    recursive
}
