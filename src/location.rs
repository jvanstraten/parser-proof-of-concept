// SPDX-License-Identifier: Apache-2.0

/// Representation of a source location. You can use this to track the
/// location in a more advanced way than just the token index (which the
/// parser tracks on its own). Note however that it's cloned a lot, so if
/// you want to track lots of immutable stuff (like a source filename),
/// consider sticking it in an Rc. The default is simply empty.
pub trait LocationTracker<I>: Clone {
    /// The type for a single location.
    type Location: PartialEq;

    /// The type for spans between two of these locations.
    type Span: PartialEq;

    /// Advances the source location past the given token.
    fn advance(&mut self, token: &I);

    /// Constructs a location object from the current location data in the
    /// tracker and the given corresponding token index.
    fn location(&self, index: usize) -> Self::Location;

    /// Constructs a span from this location to the other location.
    fn spanning_to(&self, from_index: usize, to: &Self, to_index: usize) -> Self::Span;
}

/// The simplest form of location is just a usize index, with Range<usize>
/// as the span type.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Simple();

impl<I> LocationTracker<I> for Simple {
    type Location = usize;
    type Span = std::ops::Range<usize>;

    fn advance(&mut self, _token: &I) {}

    fn location(&self, index: usize) -> Self::Location {
        index
    }

    fn spanning_to(&self, from_index: usize, _to: &Self, to_index: usize) -> Self::Span {
        from_index..to_index
    }
}

/// A location that tracks source file and row/column/byte location.
#[derive(Debug, PartialEq)]
pub struct Rich<I: ?Sized, F: Fn(&I) -> &str> {
    /// Immutable data; the source filename and the token-to-str converter.
    immutable: std::rc::Rc<(std::rc::Rc<String>, F)>,

    /// Current row (1-based).
    row: usize,

    /// Current column (1-based).
    column: usize,

    /// Current byte offset (0-based).
    offset: usize,

    phantom: std::marker::PhantomData<I>,
}

impl<I, F: Fn(&I) -> &str> Clone for Rich<I, F> {
    fn clone(&self) -> Self {
        Self {
            immutable: self.immutable.clone(),
            row: self.row,
            column: self.column,
            offset: self.offset,
            phantom: self.phantom,
        }
    }
}

impl<I, F: Fn(&I) -> &str> Rich<I, F> {
    pub fn new<S: ToString>(source_file: S, converter: F) -> Self {
        Self {
            immutable: std::rc::Rc::new((std::rc::Rc::new(source_file.to_string()), converter)),
            row: 1,
            column: 1,
            offset: 0,
            phantom: Default::default(),
        }
    }
}

impl<I, F: Fn(&I) -> &str> LocationTracker<I> for Rich<I, F> {
    type Location = RichLocation;
    type Span = RichSpan;

    fn advance(&mut self, token: &I) {
        let s = (self.immutable.1)(token);
        for c in s.chars() {
            if c == '\n' {
                self.row += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        self.offset += s.as_bytes().len();
    }

    fn location(&self, index: usize) -> Self::Location {
        RichLocation {
            filename: self.immutable.0.clone(),
            offset: RichOffset {
                row: self.row,
                column: self.column,
                offset: self.offset,
                index,
            },
        }
    }

    fn spanning_to(&self, from_index: usize, to: &Self, to_index: usize) -> Self::Span {
        RichSpan {
            filename: self.immutable.0.clone(),
            from: RichOffset {
                row: self.row,
                column: self.column,
                offset: self.offset,
                index: from_index,
            },
            to: RichOffset {
                row: to.row,
                column: to.column,
                offset: to.offset,
                index: to_index,
            },
        }
    }
}

/// A "rich" offset within a file, including row, column, byte offset, and
/// token index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RichOffset {
    pub row: usize,
    pub column: usize,
    pub offset: usize,
    pub index: usize,
}

impl std::fmt::Display for RichOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.row, self.column)
    }
}

/// A "rich" source location, including filename, row, column, byte offset, and
/// token index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RichLocation {
    pub filename: std::rc::Rc<String>,
    pub offset: RichOffset,
}

impl std::fmt::Display for RichLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.filename, self.offset)
    }
}

/// A "rich" source span, including filename, inclusive start offset, and
/// exclusive end offset, where both offsets include row, column, byte offset,
/// and token index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RichSpan {
    pub filename: std::rc::Rc<String>,
    pub from: RichOffset,
    pub to: RichOffset,
}

impl std::fmt::Display for RichSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}..{}", self.filename, self.from, self.to)
    }
}
