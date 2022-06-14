use super::parser;
use super::location;
use super::error;

pub struct Just<'i, I, O, L, E>
where
    I: 'i + PartialEq,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    expected: &'i O,
    phantom: std::marker::PhantomData<(L, E)>,
}

impl<'i, I, O, L, E> parser::Parser<'i, I, L, E> for Just<'i, I, O, L, E>
where
    I: 'i + PartialEq,
    O: Clone,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    type Output = &'i O;
    
    fn parse_internal(
        &self,
        stream: &mut crate::stream::Stream<I, L>,
        enable_recovery: bool,
    ) -> parser::Result<Self::Output, E> {
        // Save the initial parser state, so we can restore it if we encounter
        // an error.
        let initial = stream.save();

        // Match concatenation of tokens returned by expected.
        for expected in (&self.expected).into_iter() {
            let found = stream.token();
            if found == Some(expected) {
                stream.advance();
            } else {

                // Get error information from the stream, then restore it to
                // the initial position.
                let successful_up_to = stream.index();
                let from = stream.save();
                stream.advance();
                let span = stream.spanning_back_to(&from);
                drop(from);
                stream.restore(&initial);
                drop(initial);

                // Construct error message.
                return parser::Result::Failed(successful_up_to, E::expected_found([Some(expected)], found, span))
            }
        }

        // All elements were matched successfully.
        return parser::Result::Success(self.expected)
    }
}

pub fn just<'i, I, O, L, E>(expected: &'i O) -> Just<'i, I, O, L, E>
where
    I: 'i + PartialEq,
    O: Clone,
    &'i O: IntoIterator<Item = &'i I>,
    L: location::LocationTracker<I>,
    E: error::Error<'i, I, L>,
{
    Just {
        expected,
        phantom: std::marker::PhantomData::default(),
    }
}

