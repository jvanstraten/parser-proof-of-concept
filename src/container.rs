/// A utility trait to abstract over container-like things, used at the input
/// of things like just(), one_of(), and none_of().
pub trait Container<'t, T>
where
    Self: 't,
{
    /// An iterator over the items within this container.
    type Iter: Iterator<Item = T>;

    /// Iterate over the elements of the container.
    fn get_iter(&'t self) -> Self::Iter;
}

impl<'t, T: Clone> Container<'t, T> for T
where
    Self: 't,
{
    type Iter = core::iter::Once<T>;
    fn get_iter(&'t self) -> Self::Iter {
        core::iter::once(self.clone())
    }
}

impl<'t, T> Container<'t, &'t T> for T
where
    Self: 't,
{
    type Iter = core::iter::Once<&'t T>;
    fn get_iter(&'t self) -> Self::Iter {
        core::iter::once(self)
    }
}

impl<'t> Container<'t, char> for String
where
    Self: 't,
{
    type Iter = std::str::Chars<'t>;
    fn get_iter(&'t self) -> Self::Iter {
        self.chars()
    }
}

impl<'t> Container<'t, char> for &'t str
where
    Self: 't,
{
    type Iter = std::str::Chars<'t>;
    fn get_iter(&'t self) -> Self::Iter {
        self.chars()
    }
}

impl<'t, T: Clone> Container<'t, T> for [T]
where
    Self: 't,
{
    type Iter = core::iter::Cloned<core::slice::Iter<'t, T>>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter().cloned()
    }
}

impl<'t, T: Clone> Container<'t, &'t T> for [T]
where
    Self: 't,
{
    type Iter = core::slice::Iter<'t, T>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter()
    }
}

impl<'t, T: Clone, const N: usize> Container<'t, T> for [T; N]
where
    Self: 't,
{
    type Iter = core::iter::Cloned<core::slice::Iter<'t, T>>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter().cloned()
    }
}

impl<'t, T: Clone, const N: usize> Container<'t, &'t T> for [T; N]
where
    Self: 't,
{
    type Iter = core::slice::Iter<'t, T>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter()
    }
}

impl<'t, T: Clone> Container<'t, T> for Vec<T>
where
    Self: 't,
{
    type Iter = core::iter::Cloned<core::slice::Iter<'t, T>>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter().cloned()
    }
}

impl<'t, T: Clone> Container<'t, &'t T> for Vec<T>
where
    Self: 't,
{
    type Iter = core::slice::Iter<'t, T>;
    fn get_iter(&'t self) -> Self::Iter {
        self.iter()
    }
}

// etc.
