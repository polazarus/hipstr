use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, offset_of, transmute};
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use super::{OwnedRepr, Repr};
use crate::backend::{self, Backend, Counter, UpdateResult};
use crate::common::header::Header;
use crate::common::tagged_pointer::TaggedPointer;
use crate::common::utils::drop_raw_slice;
use crate::common::{methods, unwrap_display};
use crate::thin::{self, TryReserveError, TryReserveErrorKind};

pub type InlineBase<T> = crate::inline::base::Base<T, crate::inline::layouts::BasicLayout>;

pub const SLICE_TAG: usize = 0b10;
pub const SLICE_TAG_MASK: usize = 0b11;

#[repr(C)]
struct Pivot {
    #[cfg(target_endian = "little")]
    lsw: NonNull<()>,
    rest: [MaybeUninit<*mut ()>; 2],
    #[cfg(target_endian = "big")]
    lsw: NonNull<()>,
}

const _ASSERT_PIVOT: () = {
    assert!(size_of::<Pivot>() == 3 * size_of::<*mut ()>());
    assert!(size_of::<Option<Pivot>>() == 3 * size_of::<*mut ()>());
    assert!(align_of::<Pivot>() == align_of::<*mut ()>());
    assert!(offset_of!(Pivot, lsw) == 0);
};

#[repr(C)]
struct LswAccess {
    #[cfg(target_endian = "little")]
    lsw: NonZeroUsize,
    _rest: [MaybeUninit<*mut ()>; 2],
    #[cfg(target_endian = "big")]
    lsw: NonZeroUsize,
}

const _ASSERT_LSW: () = {
    assert!(size_of::<LswAccess>() == size_of::<Pivot>());
    assert!(size_of::<Option<LswAccess>>() == size_of::<Option<Pivot>>());
    assert!(align_of::<LswAccess>() == align_of::<Pivot>());
    assert!(offset_of!(LswAccess, lsw) == offset_of!(Pivot, lsw));
};

#[derive(Debug)]
#[repr(transparent)]
pub(crate) struct Owner<T, P>(TaggedPointer<Header<T, P, Option<NonNull<T>>>, SLICE_TAG>);

impl<T, P> Copy for Owner<T, P> {}

impl<T, P> Clone for Owner<T, P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, P: Counter> Owner<T, P> {
    #[inline]
    pub(crate) const fn none() -> Self {
        Self(TaggedPointer::null())
    }

    pub(crate) const fn from_thin(thin: thin::Base<T, P>) -> Self {
        // SAFETY: same repr
        // The ptr field is None in Owner because it's zero in thin::Base.
        unsafe { transmute::<thin::Base<T, P>, Owner<T, P>>(thin) }
    }

    pub(crate) fn from_wide(vec: Vec<T>) -> Self {
        Self(TaggedPointer::from(Header::from_wide(vec)))
    }

    const unsafe fn as_thin_mut_unchecked(&mut self) -> &mut thin::Base<T, P> {
        unsafe { transmute::<&mut Self, &mut thin::Base<T, P>>(self) }
    }

    unsafe fn drop(&mut self) {
        if let Some(header) = self.0.as_non_null() {
            match unsafe { header.as_ref().prefix.decr() } {
                UpdateResult::Done => {
                    // nothing to do, the counter was decremented successfully
                }
                UpdateResult::Overflow => {
                    if unsafe { header.as_ref().ptr.is_none() } {
                        // thin
                        unsafe {
                            self.as_thin_mut_unchecked().drop();
                        }
                    } else {
                        // wide
                        todo!()
                    }
                }
            }
        }
    }

    unsafe fn drop_container(&mut self)
    where
        T: Copy,
    {
        if let Some(header) = self.0.as_non_null() {
            match unsafe { header.as_ref().prefix.decr() } {
                UpdateResult::Done => {
                    // nothing to do, the counter was decremented successfully
                }

                UpdateResult::Overflow => {
                    unsafe {
                        if header.as_ref().ptr.is_none() {
                            // thin
                            self.as_thin_mut_unchecked().drop_container();
                        } else {
                            // wide
                            todo!()
                        }
                    }
                }
            }
        }
    }

    const fn is_some(&self) -> bool {
        self.0.as_non_null().is_some()
    }

    const fn is_none(&self) -> bool {
        self.0.as_non_null().is_none()
    }

    const fn set_len(&self, new_len: usize) {
        if let Some(mut header) = self.0.as_non_null() {
            let header = unsafe { header.as_mut() };
            header.len = new_len;
        } else {
            debug_assert!(new_len == 0, "cannot set non-zero length on a none owner");
        }
    }
}

pub enum OwnerMut<'a, T, P> {
    Thin(&'a mut thin::Base<T, P>),
    Wide(), // TODO
}

#[repr(C)]
pub struct Sliced<T, C: Counter> {
    #[cfg(target_endian = "little")]
    owner: Owner<T, C>,

    slice: NonNull<[T]>,

    #[cfg(target_endian = "big")]
    owner: Owner<T, C>,
}

const _ASSERT_SLICED: () = {
    type C = backend::Count;

    assert!(size_of::<Sliced<(), C>>() == size_of::<Pivot>());
    assert!(size_of::<Option<Sliced<(), C>>>() == size_of::<Option<Pivot>>());
    assert!(align_of::<Sliced<(), C>>() == align_of::<Pivot>());
    assert!(offset_of!(Sliced<(), C>, owner) == offset_of!(Pivot, lsw));
};

enum Either<T, F> {
    Thin(T),
    Wide(F),
}

impl<T, C: Counter> Sliced<T, C> {
    const fn borrowed(slice: NonNull<[T]>) -> Self {
        Self {
            owner: Owner::none(),
            slice,
        }
    }

    const fn from_thin(thin: thin::Base<T, C>) -> Self {
        let slice = NonNull::from_ref(thin.as_slice());
        Self {
            owner: Owner::from_thin(thin),
            slice,
        }
    }

    unsafe fn drop(&mut self) {
        self.slice = NonNull::from_ref(&[]);

        unsafe {
            self.owner.drop();
        }
    }

    unsafe fn drop_copy(&mut self)
    where
        T: Copy,
    {
        self.slice = NonNull::from_ref(&[]);

        unsafe {
            self.owner.drop_container();
        }
    }

    fn is_unique(&self) -> bool {
        if let Some(header) = self.owner.0.as_non_null() {
            unsafe { header.as_ref().prefix.is_unique() }
        } else {
            unsafe { self.slice.as_ref() }.is_empty()
        }
    }

    fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        if self.is_unique() {
            Some(unsafe { self.slice.as_mut() })
        } else {
            None
        }
    }

    const unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [T] {
        unsafe { self.slice.as_mut() }
    }

    const fn has_owner(&self) -> bool {
        self.owner.is_some()
    }

    #[inline]
    const fn repr(&self) -> Option<OwnedRepr> {
        if self.owner.is_some() {
            let header = unsafe { self.owner.0.as_non_null().unwrap().as_ref() };
            if header.ptr.is_none() {
                Some(OwnedRepr::Thin)
            } else {
                Some(OwnedRepr::Wide)
            }
        } else {
            None
        }
    }

    #[inline]
    fn from_wide(vec: Vec<T>) -> Self {
        let slice = NonNull::from_ref(vec.as_slice());
        Self {
            owner: Owner::from_wide(vec),
            slice,
        }
    }
}

const _: () = {
    type C = backend::Count;

    assert!(size_of::<Pivot>() == size_of::<Sliced<(), C>>());
    assert!(align_of::<Pivot>() == align_of::<Sliced<(), C>>());
    assert!(offset_of!(Pivot, lsw) == offset_of!(Sliced<(), C>, owner));
};

impl<T, C: Counter> Copy for Sliced<T, C> {}
impl<T, C: Counter> Clone for Sliced<T, C> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(transparent)]
pub struct Base<'a, T, B: Backend> {
    inner: Pivot,
    marker: PhantomData<(&'a mut [T], *const B::Counter, T)>,
}

impl<'a, T, B: Backend> Base<'a, T, B> {
    const fn lsw(&self) -> usize {
        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { transmute::<&Pivot, &LswAccess>(&self.inner) }
            .lsw
            .get()
    }

    pub const fn is_inline(&self) -> bool {
        self.lsw() & 1 == 1
    }

    pub fn is_unique(&self) -> bool {
        self.is_inline() || unsafe { self.sliced_unchecked().is_unique() }
    }

    pub const fn is_sliced(&self) -> bool {
        self.lsw() & SLICE_TAG_MASK == SLICE_TAG
    }

    #[inline]
    pub const fn repr(&self) -> Repr {
        if self.is_inline() {
            Repr::Inline
        } else {
            debug_assert!(self.is_sliced(), "must be sliced");

            let allocated = unsafe { self.sliced_unchecked() };
            if let Some(repr) = allocated.repr() {
                Repr::Owned(repr)
            } else {
                Repr::Borrowed
            }
        }
    }

    pub const fn from_borrowed_slice(slice: &[T]) -> Self {
        Self::from_sliced(Sliced::borrowed(NonNull::from_ref(slice)))
    }

    pub fn from_wide(vec: Vec<T>) -> Self {
        Self::from_sliced(Sliced::from_wide(vec))
    }

    const fn from_sliced(sliced: Sliced<T, B::Counter>) -> Self {
        Self {
            inner: unsafe { transmute::<Sliced<T, B::Counter>, Pivot>(sliced) },
            marker: PhantomData,
        }
    }

    fn from_thin_base(thin: thin::Base<T, B::Counter>) -> Self {
        Self::from_sliced(Sliced::from_thin(thin))
    }

    pub fn from_any_thin_base<P>(mut vec: thin::Base<T, P>) -> Self {
        if compatible_prefix::<P, B::Counter>() || vec.len() > InlineBase::<T>::CAPACITY {
            // either the prefix is compatible, or the vec is too big for the inline base
            // in both cases we want a thin base with the correct prefix

            let thin = vec.with_fresh_prefix();
            Self::from_thin_base(thin)
        } else {
            // the prefix is not compatible, but the vec is small enough for the inline base

            let mut base: InlineBase<T> = InlineBase::new();
            methods::append!(&mut base, &mut vec);
            Self::from_inline_base(base)
        }
    }

    pub const unsafe fn inline_unchecked(&self) -> &InlineBase<T> {
        debug_assert!(self.is_inline());

        // SAFETY: Type invariant
        unsafe { transmute::<&Self, &InlineBase<T>>(self) }
    }

    pub const unsafe fn inline_mut_unchecked(&mut self) -> &mut InlineBase<T> {
        debug_assert!(self.is_inline());

        // SAFETY: Type invariant
        unsafe { transmute::<&mut Self, &mut InlineBase<T>>(self) }
    }

    /// Retuns a mutable reference to the sliced base.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that the base is actually a sliced base, and not an inline one.
    ///
    /// See [`is_sliced`](Self::is_sliced) to check if the representation is sliced.
    pub const unsafe fn sliced_unchecked(&self) -> &Sliced<T, B::Counter> {
        debug_assert!(self.is_sliced());

        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { transmute(self) }
    }

    /// Retuns a mutable reference to the sliced base.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that the base is actually a sliced base, and not an inline one.
    /// Additionally, the caller must guarantee that they have unique access to the base, as this returns a mutable reference.
    ///
    /// See [`is_sliced`](Self::is_sliced) to check if the representation is sliced.
    pub const unsafe fn sliced_unchecked_mut(&mut self) -> &mut Sliced<T, B::Counter> {
        debug_assert!(self.is_sliced());

        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { transmute(self) }
    }

    const fn from_inline_base(inline: InlineBase<T>) -> Self {
        let pivot = unsafe { transmute::<InlineBase<T>, Pivot>(inline) };
        Self {
            inner: pivot,
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn new() -> Self {
        Self::from_inline_base(InlineBase::new())
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::from_sliced(Sliced::from_thin(thin::Base::with_capacity(capacity)))
    }

    pub const fn as_ptr(&self) -> *const T {
        if self.is_inline() {
            unsafe { self.inline_unchecked().as_ptr() }
        } else {
            unsafe { self.sliced_unchecked().slice.as_ref().as_ptr() }
        }
    }

    pub const fn as_slice(&self) -> &[T] {
        if self.is_inline() {
            unsafe { self.inline_unchecked().as_slice() }
        } else {
            unsafe { self.sliced_unchecked().slice.as_ref() }
        }
    }

    pub const fn len(&self) -> usize {
        if self.is_inline() {
            unsafe { self.inline_unchecked().len() }
        } else {
            unsafe { self.sliced_unchecked().slice.as_ref().len() }
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn inline_mut(&mut self) -> Option<&mut InlineBase<T>> {
        if self.is_inline() {
            Some(unsafe { self.inline_mut_unchecked() })
        } else {
            None
        }
    }

    #[inline]
    pub const fn sliced_or_inline(&mut self) -> SlicedOrInlineMut<'_, T, B> {
        if self.is_inline() {
            SlicedOrInlineMut::Inline(unsafe { self.inline_mut_unchecked() })
        } else {
            SlicedOrInlineMut::Sliced(unsafe { self.sliced_unchecked_mut() })
        }
    }

    pub unsafe fn drop(&mut self) {
        match self.sliced_or_inline() {
            SlicedOrInlineMut::Inline(inline) => unsafe {
                inline.set_len(0);
                drop_raw_slice(inline.as_mut_ptr(), inline.len());
            },
            SlicedOrInlineMut::Sliced(sliced) => unsafe {
                sliced.drop();
            },
        }
    }

    pub unsafe fn drop_copy(&mut self)
    where
        T: Copy,
    {
        match self.sliced_or_inline() {
            SlicedOrInlineMut::Inline(inline) => unsafe {
                inline.set_len(0);
            },
            SlicedOrInlineMut::Sliced(sliced) => unsafe {
                sliced.drop_copy();
            },
        }
    }

    pub fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        match self.sliced_or_inline() {
            SlicedOrInlineMut::Inline(inline) => Some(inline.as_mut_slice()),
            SlicedOrInlineMut::Sliced(sliced) => sliced.as_mut_slice(),
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        match self.sliced_or_inline() {
            SlicedOrInlineMut::Inline(inline) => inline.as_mut_ptr(),
            SlicedOrInlineMut::Sliced(sliced) => sliced.slice.cast().as_ptr(),
        }
    }

    pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [T] {
        match self.sliced_or_inline() {
            SlicedOrInlineMut::Inline(inline) => inline.as_mut_slice(),
            SlicedOrInlineMut::Sliced(sliced) => unsafe { sliced.slice.as_mut() },
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_mut_slice(&mut self) -> &mut [T]
    where
        T: Clone,
    {
        self.make_unique_clone();

        unsafe { self.as_mut_slice_unchecked() }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_mut_slice_copy(&mut self) -> &mut [T]
    where
        T: Copy,
    {
        self.make_unique_copy();

        unsafe { self.as_mut_slice_unchecked() }
    }

    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.is_empty() {
            Self::new()
        } else if slice.len() <= InlineBase::<T>::CAPACITY {
            Self::from_inline_base(InlineBase::from_slice(slice))
        } else {
            Self::from_thin_base(thin::Base::from_slice(slice))
        }
    }

    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        if slice.is_empty() {
            Self::new()
        } else if slice.len() <= InlineBase::<T>::CAPACITY {
            Self::from_inline_base(InlineBase::from_slice_copy(slice))
        } else {
            Self::from_thin_base(thin::Base::from_slice_copy(slice))
        }
    }

    pub fn make_unique_clone(&mut self)
    where
        T: Clone,
    {
        if self.is_unique() {
            // nothing to do
        } else {
            let sliced = unsafe { self.sliced_unchecked_mut() };
            *self = Self::from_slice(unsafe { sliced.slice.as_ref() });
            debug_assert!(self.is_unique());
        }
    }

    pub fn make_unique_copy(&mut self)
    where
        T: Copy,
    {
        if self.is_unique() {
            // nothing to do
        } else {
            let sliced = unsafe { self.sliced_unchecked_mut() };
            *self = Self::from_slice_copy(unsafe { sliced.slice.as_ref() });
            debug_assert!(self.is_unique());
        }
    }

    pub fn mutate_unchecked(&mut self) -> Mut<'_, 'a, T, B> {
        debug_assert!(self.is_unique());

        Mut { base: self }
    }
}

pub enum SlicedOrInlineMut<'a, T, B: Backend> {
    Sliced(&'a mut Sliced<T, B::Counter>),
    Inline(&'a mut InlineBase<T>),
}

const _ASSERT_BASE: () = {
    type B = backend::Rc;
    assert!(size_of::<Base<(), B>>() == 3 * size_of::<usize>());
    assert!(size_of::<Option<Base<(), B>>>() == size_of::<Base<(), B>>());
    assert!(align_of::<Base<(), B>>() == align_of::<usize>());
};

const fn compatible_prefix<P1, P2>() -> bool {
    size_of::<P1>() == size_of::<P2>() && align_of::<P1>() == align_of::<P2>()
}

pub struct Mut<'a, 'b, T, B: Backend> {
    base: &'a mut Base<'b, T, B>,
}

impl<'a, 'b, T, B: Backend> Mut<'a, 'b, T, B> {
    #[inline]
    pub fn len(&self) -> usize {
        self.base.len()
    }

    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        if self.base.is_inline() {
            unsafe { self.base.inline_mut_unchecked().set_len(new_len) }
        } else {
            let sliced = unsafe { self.base.sliced_unchecked_mut() };
            debug_assert!(sliced.has_owner() || new_len == 0);
            sliced.owner.set_len(new_len);
            slice_set_len(&mut sliced.slice, new_len);
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { self.base.as_mut_slice_unchecked() }
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.base.as_mut_ptr()
    }

    pub fn push_mut(&mut self, value: T) -> &mut T {
        methods::push_mut!(self, value)
    }

    pub fn reserve(&mut self, additional: usize) {
        unwrap_display(self.try_reserve(additional));
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let required = self
            .len()
            .checked_add(additional)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?;

        if self.base.is_inline() {
            if required <= InlineBase::<T>::CAPACITY {
                // nothing to do
            } else {
                // need to move to a thin base
                let mut new_base: thin::Base<T, B::Counter> = thin::Base::with_capacity(required);
                methods::append!(&mut new_base, unsafe { self.base.inline_mut_unchecked() });

                // nothing to drop in the inline base, as all the elements were
                // moved to the thin base, and there is no allocation for inline
                *self.base = Base::from_thin_base(new_base);
            }
        } else {
            let sliced = unsafe { self.base.sliced_unchecked_mut() };
            match sliced.repr() {
                Some(OwnedRepr::Thin) => {
                    let thin = unsafe { sliced.owner.as_thin_mut_unchecked() };
                    thin.try_reserve(additional)?;
                    sliced.slice = NonNull::from_ref(thin.as_slice());
                }
                Some(OwnedRepr::Wide) => {
                    let mut thin: thin::Base<T, <B as Backend>::Counter> =
                        thin::Base::with_capacity(required);
                    unsafe {
                        thin.as_mut_ptr().copy_from_nonoverlapping(
                            sliced.slice.as_ptr().cast(),
                            sliced.slice.len(),
                        );
                        thin.set_len(sliced.slice.len());
                        sliced.owner.set_len(0);
                        sliced.slice = NonNull::from_ref(&[]);
                    }
                    *sliced = Sliced::from_thin(thin);
                }
                None => {
                    let thin = thin::Base::with_capacity(required);
                    *sliced = Sliced::from_thin(thin);
                }
            }
        }
        Ok(())
    }
}

const fn slice_set_len<T>(slice: &mut NonNull<[T]>, new_len: usize) {
    let ptr: NonNull<T> = slice.cast();
    let new_slice = NonNull::slice_from_raw_parts(ptr, new_len);
    *slice = new_slice;
}
