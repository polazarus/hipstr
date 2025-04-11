use crate::smart::{Kind, Smart, UpdateResult};

#[macro_export]
macro_rules! smart_thin_vec {
    [$t:ty :] => {
        $crate::vecs::SmartThinVec::<_, $t>::new()
    };
    [$t:ty : $e:expr ; $l:expr] => {{
        use $crate::vecs::thin::{SmartThinVec, SmartPrefix, PrefixedThinVec};

        let len = $l;
        let mut vec = PrefixedThinVec::with_capacity(SmartPrefix::<$t>::new(), len);
        vec.extend_with(len, $e);
        SmartThinVec::from_owned(vec)
    }};

    [$t:ty : $($e:expr),+ $(,)?] => {{
        use $crate::vecs::thin::{SmartThinVec, SmartPrefix, PrefixedThinVec};

        let mut vec = PrefixedThinVec::with_capacity(SmartPrefix::<$t>::new(), thin_vec!(@count $( ($e) )+));
        $(
            vec.push($e);
        )+
        SmartThinVec::from_owned(vec)
    }};
    [$($t:tt)*] => { smart_thin_vec![$crate::Arc : $($t)*]}
}

/// A smart prefix for smart thin vectors.
pub struct SmartPrefix<C: Kind> {
    count: C,
    ptr: ZeroUsize,
}

impl<C: Kind> SmartPrefix<C> {
    #[doc(hidden)]
    pub fn new() -> Self {
        Self {
            count: C::one(),
            ptr: ZeroUsize::Zero,
        }
    }
}

#[repr(transparent)]
pub struct SmartThinVec<T, C: Kind>(pub(super) NonNull<Header<T, SmartPrefix<C>>>);

impl<T, C: Kind> SmartThinVec<T, C> {
    #[doc(hidden)]
    pub fn from_owned(thin: PrefixedThinVec<T, SmartPrefix<C>>) -> Self {
        unsafe { mem::transmute(thin) }
    }

    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        Self::from_owned(PrefixedThinVec::from_slice_copy(SmartPrefix::new(), slice))
    }

    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        Self::from_owned(PrefixedThinVec::from_slice_clone(SmartPrefix::new(), slice))
    }

    pub fn new() -> Self {
        Self::from_owned(PrefixedThinVec::new(SmartPrefix::new()))
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self::from_owned(PrefixedThinVec::with_capacity(SmartPrefix::new(), capacity))
    }

    fn count(&self) -> &C {
        &self.header().prefix.count
    }

    pub unsafe fn mutate_unchecked(&mut self) -> &mut PrefixedThinVec<T, SmartPrefix<C>> {
        unsafe { mem::transmute(self) }
    }

    pub fn mutate(&mut self) -> Option<&mut PrefixedThinVec<T, SmartPrefix<C>>> {
        if self.count().is_unique() {
            Some(unsafe { self.mutate_unchecked() })
        } else {
            None
        }
    }

    pub const fn as_vec(&self) -> &PrefixedThinVec<T, SmartPrefix<C>> {
        unsafe { mem::transmute(self) }
    }
}

impl<T, C: Kind> ops::Deref for SmartThinVec<T, C> {
    type Target = PrefixedThinVec<T, SmartPrefix<C>>;

    fn deref(&self) -> &Self::Target {
        self.as_vec()
    }
}

impl<T, C: Kind> From<&[T]> for SmartThinVec<T, C>
where
    T: Clone,
{
    fn from(slice: &[T]) -> Self {
        Self::from_slice_clone(slice)
    }
}

impl<C: Kind, T, const N: usize> From<[T; N]> for SmartThinVec<T, C>
where
    T: Clone,
{
    fn from(array: [T; N]) -> Self {
        Self::from_slice_clone(&array)
    }
}

impl<T, C: Kind> Clone for SmartThinVec<T, C> {
    fn clone(&self) -> Self {
        if self.count().incr() == UpdateResult::Overflow {
            panic!("count overflow");
        } else {
            Self(self.0)
        }
    }
}

impl<T, C: Kind> Drop for SmartThinVec<T, C> {
    fn drop(&mut self) {
        if self.count().decr() == UpdateResult::Overflow {
            unsafe {
                ptr::drop_in_place(self.mutate_unchecked());
            }
        }
    }
}
