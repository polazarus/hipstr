use alloc::borrow::ToOwned;
use core::borrow::Borrow;
use core::fmt;
use core::ops::Deref;

/// A simple enum to represent a borrowed or owned value.
///
/// Relaxed version of `Cow` that does not require `Clone` on the owned type.
/// This is useful for cases where you want to avoid the overhead of cloning
/// but still want to handle both borrowed and owned values in a unified way.
#[derive(Clone)]
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

impl<T, R> Deref for Boo<'_, T, R>
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
    pub const fn into_copy(self) -> T {
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
    pub const fn is_borrowed(&self) -> bool {
        matches!(self, Self::Borrowed(..))
    }

    /// Returns `true` if the boo is [`Owned`].
    ///
    /// [`Owned`]: Boo::Owned
    #[must_use]
    pub const fn is_owned(&self) -> bool {
        matches!(self, Self::Owned(..))
    }
}

impl<T, R> Borrow<R> for Boo<'_, T, R>
where
    T: Borrow<R>,
{
    fn borrow(&self) -> &R {
        match self {
            Boo::Borrowed(b) => b,
            Boo::Owned(o) => o.borrow(),
        }
    }
}

impl<T, R> fmt::Debug for Boo<'_, T, R>
where
    T: fmt::Debug,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &Boo::Borrowed(b) => fmt::Debug::fmt(b, f),
            Boo::Owned(o) => fmt::Debug::fmt(o, f),
        }
    }
}

impl<T1, R1, T2, R2> PartialEq<Boo<'_, T2, R2>> for Boo<'_, T1, R1>
where
    T1: Borrow<R1>,
    T2: Borrow<R2>,
    R1: PartialEq<R2>,
{
    fn eq(&self, other: &Boo<'_, T2, R2>) -> bool {
        let this: &R1 = self.borrow();
        this == other.borrow()
    }
}

impl<T, R> Eq for Boo<'_, T, R>
where
    T: Borrow<R>,
    R: Eq,
{
}

impl<T1, R1, T2, R2> PartialOrd<Boo<'_, T2, R2>> for Boo<'_, T1, R1>
where
    T1: Borrow<R1>,
    T2: Borrow<R2>,
    R1: PartialOrd<R2>,
{
    fn partial_cmp(&self, other: &Boo<'_, T2, R2>) -> Option<core::cmp::Ordering> {
        let this: &R1 = self.borrow();
        this.partial_cmp(other.borrow())
    }
}

// Conversion to and from std's Cow
mod conv {
    use alloc::borrow::{Cow, ToOwned};

    use super::Boo;

    impl<'a, T, R> From<Boo<'a, T, R>> for Cow<'a, R>
    where
        R: ToOwned<Owned = T>,
    {
        fn from(value: Boo<'a, T, R>) -> Self {
            match value {
                Boo::Borrowed(b) => Cow::Borrowed(b),
                Boo::Owned(o) => Cow::Owned(o),
            }
        }
    }
    impl<'a, T, R> From<Cow<'a, R>> for Boo<'a, T, R>
    where
        R: ToOwned<Owned = T>,
    {
        fn from(value: Cow<'a, R>) -> Self {
            match value {
                Cow::Borrowed(b) => Boo::Borrowed(b),
                Cow::Owned(o) => Boo::Owned(o),
            }
        }
    }
}
