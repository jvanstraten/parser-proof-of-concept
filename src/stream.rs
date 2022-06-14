use super::location;
use std::collections::VecDeque;

/// Opaque object representing a saved stream state.
pub struct SavedState {
    index: std::rc::Rc<usize>,
}

/// A stream of tokens that can backtrack to arbitrary positions that were
/// previously saved.
pub struct Stream<'i, I, L>
where
    I: 'i,
    L: location::LocationTracker<I>,
{
    /// Iterator representing the source of the tokens.
    source: Box<dyn Iterator<Item = &'i I> + 'i>,

    /// Whether the source iterator has returned None.
    source_at_eof: bool,

    /// Location tracker tracking the location of the next token in the source
    /// iterator.
    source_location: L,

    /// Buffer to support backtracking. The back of the queue is the token that
    /// was most recently consumed from the iterator; the front is the oldest
    /// token that we may still have to backtrack to (or perhaps something
    /// older).
    buffer: VecDeque<(Option<&'i I>, L)>,

    /// The index of the next token relative to the front of the buffer.
    index_in_buffer: usize,

    /// The index of the next token relative to the start of the input.
    index: usize,

    /// All indices of tokens we may still have to backtrack to. We use weak
    /// Rcs to track which markers are in scope.
    backtrack_markers: Vec<std::rc::Weak<usize>>,
}

impl<'i, I, L> Stream<'i, I, L>
where
    I: 'i,
    L: location::LocationTracker<I>,
{
    /// Constructs a token stream from an iterable, using the default start
    /// location.
    pub fn new<J>(source: J) -> Self
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
        L: Default,
    {
        Self {
            source: Box::new(source.into_iter()),
            source_at_eof: false,
            source_location: Default::default(),
            buffer: VecDeque::new(),
            index_in_buffer: 0,
            index: 0,
            backtrack_markers: vec![],
        }
    }

    /// Constructs a token stream from an iterable and an initial start location.
    pub fn new_with_location<J>(source: J, start_location: L) -> Self
    where
        J: IntoIterator<Item = &'i I>,
        J::IntoIter: 'i,
    {
        Self {
            source: Box::new(source.into_iter()),
            source_at_eof: false,
            source_location: start_location,
            buffer: VecDeque::new(),
            index_in_buffer: 0,
            index: 0,
            backtrack_markers: vec![],
        }
    }

    /// Saves the current location, so it can be restored later.
    pub fn save(&mut self) -> SavedState {
        let index = std::rc::Rc::new(self.index);
        let downgraded = std::rc::Rc::downgrade(&index);

        // If the backtrack markers vector is at capacity, try finding an empty
        // spot rather than reallocating.
        if self.backtrack_markers.len() == self.backtrack_markers.capacity() {
            for old_marker in self.backtrack_markers.iter_mut().rev() {
                if old_marker.strong_count() == 0 {
                    *old_marker = downgraded;
                    return SavedState { index };
                }
            }
        }
        self.backtrack_markers.push(downgraded);
        SavedState { index }
    }

    /// Restores a location that was previously saved.
    pub fn restore(&mut self, saved_state: &SavedState) {
        assert!(*saved_state.index <= self.index);
        let amount = self.index - *saved_state.index;
        assert!(amount >= self.index_in_buffer);
        self.index_in_buffer -= amount;
        self.index -= amount;
    }

    /// Returns the token index of the first token in the buffer.
    fn start_of_buffer(&self) -> usize {
        self.index - self.index_in_buffer
    }

    /// Ensures that the next token is available in the buffer. This only fails
    /// if the next token is EOF. Returns whether a new token is available, so
    /// !EOF.
    fn make_next_available(&mut self) -> bool {
        // Return immediately if the next token is buffered.
        if self.index_in_buffer < self.buffer.len() {
            return true;
        }

        // If the source has previously returned EOF, don't query it again.
        if self.source_at_eof {
            return false;
        }

        // Query the source iterator. If there is none, return without doing
        // anything to signal EOF.
        if let Some(next_token) = self.source.next() {
            // Clone the state of the location tracker, to store with the token
            // in the buffer.
            let next_location = self.source_location.clone();

            // Advance the location tracker accordingly.
            self.source_location.advance(next_token);

            // If the buffer is at capacity, see if we can drop some stuff.
            if self.buffer.len() == self.buffer.capacity() {
                // Remove markers that have gone out of scope.
                self.backtrack_markers.retain(|x| x.strong_count() > 0);

                // Compute the index of the oldest token that we can still
                // backtrack to.
                let backtrack_index = self
                    .backtrack_markers
                    .iter()
                    .filter_map(|x| x.upgrade())
                    .map(|x| *x)
                    .min()
                    .unwrap_or(self.index);

                // Compute the index at the start of the buffer.
                let start_of_buffer = self.start_of_buffer();

                // Determine how many tokens we can remove from the front of
                // the buffer.
                assert!(backtrack_index >= start_of_buffer);
                if backtrack_index > start_of_buffer {
                    let remove = backtrack_index - start_of_buffer;

                    // Actually do the removal.
                    drop(self.buffer.drain(..remove));
                    assert!(self.index_in_buffer >= remove);
                    self.index_in_buffer -= remove;
                }
            }

            // Push the token into the buffer.
            self.buffer.push_back((Some(next_token), next_location));
            true
        } else {
            // Source returned EOF; store this and signal EOF.
            self.buffer.push_back((None, self.source_location.clone()));
            self.source_at_eof = true;
            false
        }
    }

    /// Returns a reference to the next token (or None for EOF) and its start
    /// location, without advancing the current location.
    pub fn token(&mut self) -> Option<&'i I> {
        // Ensure that the next token is in the buffer.
        self.make_next_available();

        // Return the next token.
        self.buffer[self.index_in_buffer].0
    }

    /// Returns a reference to the token (or None for EOF) at the given saved
    /// position. The index must have been created using save(), or this may
    /// panic (the token may not be available yet or anymore).
    pub fn token_at(&mut self, saved_state: &SavedState) -> Option<&'i I> {
        // If the index is the next token, reduce to token().
        if *saved_state.index == self.index {
            return self.token();
        }

        // Return the requested token from the buffer.
        assert!(*saved_state.index >= self.start_of_buffer());
        self.buffer[*saved_state.index - self.start_of_buffer()].0
    }

    /// Returns the token index of the next token.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the token index corresponding to the given saved state.
    pub fn index_at(&self, saved_state: &SavedState) -> usize {
        *saved_state.index
    }

    /// Returns the current state of the location tracker, placed at the start
    /// of the next token/end of the previous token.
    pub fn location_tracker(&self) -> &L {
        self.buffer
            .get(self.index_in_buffer)
            .map(|(_, x)| x)
            .unwrap_or(&self.source_location)
    }

    /// Returns the state of the location tracker as it was at the given saved
    /// state.
    pub fn location_tracker_at(&self, saved_state: &SavedState) -> &L {
        // If the index is the next token, reduce to location_tracker().
        if *saved_state.index == self.index {
            return self.location_tracker();
        }

        // Return the requested token from the buffer.
        assert!(*saved_state.index >= self.start_of_buffer());
        &self.buffer[*saved_state.index - self.start_of_buffer()].1
    }

    /// Returns the current location.
    pub fn location(&self) -> L::Location {
        self.location_tracker().location(self.index())
    }

    /// Returns the location at the given saved state.
    pub fn location_at(&self, saved_state: &SavedState) -> L::Location {
        self.location_tracker_at(saved_state)
            .location(self.index_at(saved_state))
    }

    /// Returns the span from the given saved location to the current location.
    pub fn spanning_back_to(&mut self, saved_state: &SavedState) -> L::Span {
        self.location_tracker_at(saved_state).spanning_to(
            self.index_at(saved_state),
            self.location_tracker(),
            self.index(),
        )
    }

    /// Returns whether we've reached EOF.
    pub fn eof(&mut self) -> bool {
        self.token().is_none()
    }

    /// Advances the parser to the next token. Returns true if successful, or
    /// false of EOF was encountered.
    pub fn advance(&mut self) -> bool {
        // Ensure that the next token is in the buffer. If this fails because
        // we encountered EOF, don't do anything.
        if !self.make_next_available() {
            return false;
        }

        self.index += 1;
        self.index_in_buffer += 1;
        true
    }
}