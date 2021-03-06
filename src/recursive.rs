// SPDX-License-Identifier: Apache-2.0

use super::combinator;
use super::error;
use super::parser;
use std::cell::RefCell;
use std::rc::Rc;

pub struct Recursive<'i, I, O, E> {
    #[allow(clippy::type_complexity)]
    inner: Rc<RefCell<Option<combinator::Boxed<'i, I, O, E>>>>,
}

impl<'i, I, O, E> Clone for Recursive<'i, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'i, I, O, E> Recursive<'i, I, O, E>
where
    I: Clone + 'i,
    E: error::Error<'i, I>,
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
        P: parser::Parser<'i, I, Output = O, Error = E> + 'i,
    {
        assert!(
            self.inner.borrow_mut().replace(parser.boxed()).is_none(),
            "multiple definitions for recursive parser"
        );
    }
}

impl<'i, I, O, E> parser::Parser<'i, I> for Recursive<'i, I, O, E>
where
    I: Clone + 'i,
    E: error::Error<'i, I>,
{
    type Output = O;
    type Error = E;

    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<'i, I, E::LocationTracker>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        self.inner
            .borrow()
            .as_ref()
            .expect("recursive parser is not defined")
            .parse_internal(stream, enable_recovery)
    }
}

pub fn recursive<'i, I, F, C>(f: F) -> Recursive<'i, I, C::Output, C::Error>
where
    I: Clone + 'i,
    F: FnOnce(&Recursive<'i, I, C::Output, C::Error>) -> C,
    C: parser::Parser<'i, I> + 'i,
{
    let mut recursive = Recursive::declare();
    recursive.define(f(&recursive));
    recursive
}
