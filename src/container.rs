/// A utility trait to abstract over container-like things, used at the input
/// of things like just(), one_of(), and none_of().
pub trait Container<T> {
    /// Returns an iterator over the items in the container.
    ///
    /// Why boxed and not an associated type? Because some of the iterators
    /// we want to return need a lifetime parameter that must be set to the
    /// lifetime of &self for things to work. The lifetime can't be a generic
    /// of the trait, because then it would always be too long. If there's a
    /// better solution to this puzzle (that does not require collecting things
    /// into a temporary Vec for every call to get_iter) then please do change
    /// this.
    #[allow(clippy::needless_lifetimes)] // thanks, but no thanks, I'd rather this magic be explicit
    fn get_iter<'s>(&'s self) -> BoxedIter<'s, T>;
}

/// A random iterator in a box.
pub struct BoxedIter<'t, T> {
    iter: Box<dyn Iterator<Item = T> + 't>,
}

impl<'t, T> Iterator for BoxedIter<'t, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// Trait with a blanked to define a combinator-based constructor for BoxedIter
/// on all iterators.
pub trait BoxedIterator<'t, T> {
    fn boxed(self) -> BoxedIter<'t, T>;
}

impl<'t, I, T> BoxedIterator<'t, T> for I
where
    I: Iterator<Item = T> + 't,
{
    fn boxed(self) -> BoxedIter<'t, T> {
        BoxedIter {
            iter: Box::new(self),
        }
    }
}

/// Allows single objects to be used as inputs to containers. To facilitate
/// zero-copy, T can simply be bound to a reference (which is Copy); no
/// specialization is needed for this.
impl<T: Clone> Container<T> for T {
    fn get_iter(&self) -> BoxedIter<T> {
        core::iter::once(self.clone()).boxed()
    }
}

/// Specialization for strings to allow them to be used as containers of
/// characters.
impl Container<char> for String {
    fn get_iter(&self) -> BoxedIter<char> {
        self.chars().boxed()
    }
}

/// Specialization for string slices to allow them to be used as containers of
/// characters.
impl<'t> Container<char> for &'t str {
    fn get_iter(&self) -> BoxedIter<char> {
        self.chars().boxed()
    }
}

/// Specialization for owned slices. To facilitate zero-copy, T can be bound to
/// a reference.
impl<T: Clone> Container<T> for [T] {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to slices, yielding clones of the items.
impl<'t, T: Clone> Container<T> for &'t [T] {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to slices, yielding references to the items.
impl<'t, T> Container<&'t T> for &'t [T] {
    fn get_iter(&self) -> BoxedIter<&'t T> {
        self.iter().boxed()
    }
}

/// Specialization for owned arrays. To facilitate zero-copy, T can be bound to
/// a reference.
impl<T: Clone, const N: usize> Container<T> for [T; N] {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to arrays, yielding clones of the items.
impl<'t, T: Clone, const N: usize> Container<T> for &'t [T; N] {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to arrays, yielding references to the items.
impl<'t, T, const N: usize> Container<&'t T> for &'t [T; N] {
    fn get_iter(&self) -> BoxedIter<&'t T> {
        self.iter().boxed()
    }
}

/// Specialization for vectors. To facilitate zero-copy, T can be bound to a
/// reference.
impl<T: Clone> Container<T> for Vec<T> {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to vectors, yielding clones of the items.
impl<'t, T: Clone> Container<T> for &'t Vec<T> {
    fn get_iter(&self) -> BoxedIter<T> {
        self.iter().cloned().boxed()
    }
}

/// Specialization for references to vectors, yielding references to the items.
impl<'t, T> Container<&'t T> for &'t Vec<T> {
    fn get_iter(&self) -> BoxedIter<&'t T> {
        self.iter().boxed()
    }
}

// etc.
