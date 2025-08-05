use alloc::borrow::ToOwned;
use core::ops::Deref;

/// A simple enum to represent a borrowed or owned value.
///
/// Relaxed version of `Cow` that does not require `Clone` on the owned type.
/// This is useful for cases where you want to avoid the overhead of cloning
/// but still want to handle both borrowed and owned values in a unified way.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Boo<'a, T, R = T> {
    Borrowed(&'a R),
    Owned(T),
}

impl<T, R> AsRef<R> for Boo<'_, T, R>
where
    T: AsRef<R>,
{
    fn as_ref(&self) -> &R {
        match self {
            Boo::Borrowed(b) => b,
            Boo::Owned(o) => o.as_ref(),
        }
    }
}

impl<'a, T, R> Deref for Boo<'a, T, R>
where
    T: Deref<Target = R>,
{
    type Target = R;

    fn deref(&self) -> &Self::Target {
        match self {
            Boo::Borrowed(b) => b,
            Boo::Owned(o) => o,
        }
    }
}

impl<T, R> Boo<'_, T, R>
where
    R: ToOwned<Owned = T>,
{
    pub fn into_owned(self) -> T {
        match self {
            Boo::Borrowed(b) => b.to_owned(),
            Boo::Owned(o) => o,
        }
    }

    pub fn to_mut(&mut self) -> &mut T {
        match self {
            &mut Boo::Borrowed(borrowed) => {
                *self = Boo::Owned(borrowed.to_owned());
                let Boo::Owned(r) = self else { unreachable!() };
                r
            }
            Boo::Owned(o) => o,
        }
    }
}

impl<T> Boo<'_, T>
where
    T: Copy,
{
    pub fn into_copy(self) -> T {
        match self {
            Boo::Borrowed(b) => *b,
            Boo::Owned(o) => o,
        }
    }
}

impl<T, R> Boo<'_, T, R> {
    /// Returns `true` if the boo is [`Borrowed`].
    ///
    /// [`Borrowed`]: Boo::Borrowed
    #[must_use]
    pub fn is_borrowed(&self) -> bool {
        matches!(self, Self::Borrowed(..))
    }

    /// Returns `true` if the boo is [`Owned`].
    ///
    /// [`Owned`]: Boo::Owned
    #[must_use]
    pub fn is_owned(&self) -> bool {
        matches!(self, Self::Owned(..))
    }
}
