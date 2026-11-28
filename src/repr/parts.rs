//! Neutral form of a value, to move it between representations and
//! backends without copying when the target can hold it.
//!
//! Each representation takes itself apart ([`Repr::into_parts`]) and
//! rebuilds itself from parts it can hold as they are
//! ([`Repr::try_from_parts`]), giving them back otherwise. [`convert`] ties
//! the two together, changing the backend in between, and copies only when
//! the target cannot take the parts:
//!
//! | Parts             | `Wide` | `Small`          | `Tiny`                        |
//! |-------------------|--------|------------------|-------------------------------|
//! | inline            | yes    | if it fits       | if it fits                    |
//! | borrowed          | yes    | yes              | no                            |
//! | thin buffer view  | yes    | view at start 0  | whole buffer, or unique       |
//! | adopted vector    | yes    | no               | no                            |
//!
//! A heap view that fits the target's inline capacity is copied inline
//! (normalized), which releases the buffer.
//!
//! Changing the backend keeps the buffer when it is uniquely owned (the
//! counter is rewritten in place) and copies a shared one.

use core::mem::ManuallyDrop;
use core::ptr::NonNull;

use super::Repr;
#[cfg(feature = "hip")]
use super::owner::Owner;
use crate::backend::{Backend, Counter, UpdateResult};

/// A thin buffer of a backend.
pub(crate) type ThinBase<B> = crate::thin::Base<<B as Backend>::Counter>;

/// Largest inline capacity of the representations.
pub const INLINE_MAX: usize = 3 * size_of::<usize>() - 1;

/// Up to [`INLINE_MAX`] bytes, by value.
#[derive(Clone, Copy)]
pub struct InlineBytes {
    buf: [u8; INLINE_MAX],
    len: u8,
}

impl InlineBytes {
    /// Copies `bytes`.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than [`INLINE_MAX`].
    #[inline]
    #[must_use]
    pub fn new(bytes: &[u8]) -> Self {
        let mut buf = [0; INLINE_MAX];
        buf[..bytes.len()].copy_from_slice(bytes);
        #[expect(clippy::cast_possible_truncation, reason = "at most 23")]
        Self {
            buf,
            len: bytes.len() as u8,
        }
    }

    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        &self.buf[..usize::from(self.len)]
    }
}

/// A view `start..start + len` of a thin buffer, holding one reference.
pub struct ThinView<B: Backend> {
    pub(crate) base: ThinBase<B>,
    pub(crate) start: usize,
    pub(crate) len: usize,
}

/// A view `start..start + len` of an adopted vector, holding one reference.
#[cfg(feature = "hip")]
pub struct VecView<B: Backend> {
    pub(crate) owner: Owner<B>,
    pub(crate) start: usize,
    pub(crate) len: usize,
}

/// The neutral form of a value (see the [module](self) documentation).
///
/// Dropping it releases the reference it holds, if any.
pub enum Parts<'a, B: Backend> {
    Inline(InlineBytes),
    Borrowed(&'a [u8]),
    Thin(ThinView<B>),
    #[cfg(feature = "hip")]
    Vec(VecView<B>),
}

impl<B: Backend> Drop for Parts<'_, B> {
    fn drop(&mut self) {
        match self {
            Parts::Inline(_) | Parts::Borrowed(_) => {}
            // SAFETY: the reference held by these parts, not used again
            Parts::Thin(view) => unsafe { release_thin::<B>(&mut view.base) },
            #[cfg(feature = "hip")]
            // SAFETY: same
            Parts::Vec(view) => unsafe { view.owner.release() },
        }
    }
}

/// Releases one reference to a thin buffer, freeing it on the last one.
///
/// # Safety
///
/// `base` holds a reference, not used afterwards.
unsafe fn release_thin<B: Backend>(base: &mut ThinBase<B>) {
    if base.prefix().decr() == UpdateResult::Overflow {
        // SAFETY: last reference; the bytes need no drop
        unsafe { base.drop_container() }
    }
}

impl<'a, B: Backend> Parts<'a, B> {
    /// The bytes.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        match self {
            Parts::Inline(inline) => inline.as_slice(),
            Parts::Borrowed(slice) => slice,
            Parts::Thin(view) => {
                // SAFETY: the view lies within the initialized bytes
                unsafe { core::slice::from_raw_parts(view.base.as_ptr().add(view.start), view.len) }
            }
            #[cfg(feature = "hip")]
            Parts::Vec(view) => &view.owner.as_slice()[view.start..view.start + view.len],
        }
    }

    /// Whether no other handle shares the buffer (inline and borrowed parts
    /// own nothing to share: `false`).
    fn is_unique_heap(&self) -> bool {
        match self {
            Parts::Inline(_) | Parts::Borrowed(_) => false,
            Parts::Thin(view) => view.base.prefix().is_unique(),
            #[cfg(feature = "hip")]
            Parts::Vec(view) => view.owner.is_unique(),
        }
    }

    /// Moves a unique thin view that starts past the beginning of its
    /// buffer to the start, and makes it the whole buffer (no allocation).
    /// Returns whether the parts changed.
    ///
    /// Views at the start need no compaction: every representation takes a
    /// unique one as it is.
    pub(crate) fn compact(&mut self) -> bool {
        let unique = self.is_unique_heap();
        let Parts::Thin(view) = self else {
            return false;
        };
        if !unique || view.start == 0 {
            return false;
        }
        let data = view.base.as_mut_ptr();
        // SAFETY: unique buffer, the view lies within its initialized bytes
        unsafe {
            data.copy_from(data.add(view.start), view.len);
            view.base.set_len(view.len);
        }
        view.start = 0;
        true
    }

    /// The same parts in another backend: in place for unique buffers (the
    /// counter is rewritten), given back for shared ones.
    ///
    /// # Errors
    ///
    /// Gives the parts back if they hold a shared buffer, or if the counters
    /// differ in layout.
    pub fn rebackend<B2: Backend>(self) -> Result<Parts<'a, B2>, Self> {
        if core::any::TypeId::of::<B>() == core::any::TypeId::of::<B2>() {
            let this = ManuallyDrop::new(self);
            // SAFETY: same type
            return Ok(unsafe { core::mem::transmute_copy(&*this) });
        }
        let unique = ThinBase::<B>::can_recount::<B2::Counter>() && self.is_unique_heap();
        // a held reference moves from `self` (forgotten) to the result
        let parts = match &self {
            Parts::Inline(inline) => Parts::Inline(*inline),
            Parts::Borrowed(slice) => Parts::Borrowed(slice),
            _ if !unique => return Err(self),
            Parts::Thin(view) => Parts::Thin(ThinView {
                // SAFETY: unique, allocated, layouts checked
                base: unsafe { crate::thin::Base(view.base.0).recount::<B2::Counter>() },
                start: view.start,
                len: view.len,
            }),
            #[cfg(feature = "hip")]
            Parts::Vec(view) => Parts::Vec(VecView {
                // SAFETY: unique vec owner, layouts checked
                owner: unsafe { view.owner.recount_vec::<B2>() },
                start: view.start,
                len: view.len,
            }),
        };
        core::mem::forget(self);
        Ok(parts)
    }
}

/// The thin view's data pointer at its start (with the provenance of the
/// whole allocation).
pub(crate) const fn view_ptr<B: Backend>(view: &ThinView<B>) -> NonNull<u8> {
    let mut base: ThinBase<B> = crate::thin::Base(view.base.0);
    // SAFETY: the start lies within the allocation
    unsafe { NonNull::new_unchecked(base.as_mut_ptr().add(view.start)) }
}

/// Converts between representations and backends, without copying when the
/// target can hold the value as it is (see the [module](self) documentation).
#[must_use]
pub fn convert<'a, R1: Repr<'a>, R2: Repr<'a>>(value: R1) -> R2 {
    // same representation and backend: a move. `Owned` erases the lifetime,
    // which both share (`'a`), so equal owned types mean equal types.
    if core::any::TypeId::of::<R1::Owned>() == core::any::TypeId::of::<R2::Owned>() {
        let value = ManuallyDrop::new(value);
        // SAFETY: same type
        return unsafe { core::mem::transmute_copy::<R1, R2>(&*value) };
    }
    let parts = match value.into_parts().rebackend::<R2::Backend>() {
        Ok(parts) => parts,
        Err(parts) => return R2::from_slice(parts.as_slice()),
    };
    R2::try_from_parts(parts)
        .or_else(|mut parts| {
            if parts.compact() {
                R2::try_from_parts(parts)
            } else {
                Err(parts)
            }
        })
        .unwrap_or_else(|parts| R2::from_slice(parts.as_slice()))
}
