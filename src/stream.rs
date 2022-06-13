use super::location;
use std::collections::VecDeque;

/// A stream of tokens that can backtrack to arbitrary positions that were
/// previously saved.
pub struct Stream<I, L>
where
    L: location::LocationTracker<I>,
{
    /// Iterator representing the source of the tokens.
    source: Box<dyn Iterator<Item = I>>,

    /// Whether the source iterator has returned None.
    source_at_eof: bool,

    /// Location tracker tracking the location of the next token in the source
    /// iterator.
    source_location: L,

    /// Buffer to support backtracking. The back of the queue is the token that
    /// was most recently consumed from the iterator; the front is the oldest
    /// token that we may still have to backtrack to (or perhaps something
    /// older).
    buffer: VecDeque<(I, L)>,

    /// The index of the next token relative to the front of the buffer.
    index_in_buffer: usize,

    /// The index of the next token relative to the start of the input.
    index: usize,

    /// All indices of tokens we may still have to backtrack to.
    backtrack_markers: Vec<std::rc::Weak<usize>>,
}

impl<I, L> Stream<I, L>
where
    L: location::LocationTracker<I>,
{
    /// Constructs a token stream from an iterable, using the default start
    /// location.
    pub fn new<J>(source: J) -> Self
    where
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
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
        J: IntoIterator<Item = I>,
        <J as IntoIterator>::IntoIter: 'static,
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
    pub fn save(&mut self) -> std::rc::Rc<usize> {
        let marker = std::rc::Rc::new(self.index);
        self.backtrack_markers.push(std::rc::Rc::downgrade(&marker));
        marker
    }

    /// Restores a location that was previously saved.
    pub fn restore(&mut self, index: std::rc::Rc<usize>) {
        assert!(*index <= self.index);
        let amount = self.index - *index;
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
            self.source_location.advance(&next_token);

            // If the buffer is at capacity, see if we can drop some stuff.
            if self.buffer.len() <= self.buffer.capacity() {
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
            self.buffer.push_back((next_token, next_location));
            true
        } else {
            // Source returned EOF; store this and signal EOF.
            self.source_at_eof = true;
            false
        }
    }

    /// Returns a reference to the next token and its start location and
    /// advances the location beyond it. Returns None and leaves the
    /// location as-as at EOF.
    pub fn next_token(&mut self) -> Option<&(I, L)> {
        // Ensure that the next token is in the buffer. If this fails, return
        // None to signal EOF.
        if !self.make_next_available() {
            return None;
        }

        // Advance to the next location.
        self.index += 1;
        self.index_in_buffer += 1;

        // Return the token we just skipped past.
        self.buffer.get(self.index_in_buffer - 1)
    }

    /// Returns a reference to the next token and its start location
    /// without advancing the current location. Returns None at EOF.
    pub fn peek_token(&mut self) -> Option<&(I, L)> {
        // Ensure that the next token is in the buffer. If this fails, return
        // None to signal EOF.
        if !self.make_next_available() {
            return None;
        }

        // Return the token we just skipped past.
        self.buffer.get(self.index_in_buffer - 1)
    }

    /// Returns the current state of the location tracker, placed at the start
    /// of the next token/end of the previous token.
    pub fn location(&self) -> &L {
        self.buffer
            .get(self.index_in_buffer)
            .map(|(_, x)| x)
            .unwrap_or(&self.source_location)
    }
}
