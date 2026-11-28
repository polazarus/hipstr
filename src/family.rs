//! Glue generated once per encoding family.
//!
//! Generic impls cover most traits (see [`hip`](super::hip)); what remains
//! are impls whose `Self` type is a std type, which coherence forbids writing
//! generically over the encoding.

/// Implements conversions and comparisons with the std borrowed and owned
/// forms of an encoding, in both directions.
macro_rules! impl_std_glue {
    ($enc:ty, $slice:ty, $owned:ty) => {
        $crate::family::impl_std_glue!($enc, $slice, $owned, no_box);

        impl<'a, R: $crate::repr::Repr<'a>> From<alloc::boxed::Box<$slice>>
            for $crate::hip::Hip<$enc, R>
        {
            #[inline]
            fn from(value: alloc::boxed::Box<$slice>) -> Self {
                Self::from_owned(<$owned>::from(value))
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> From<alloc::rc::Rc<$slice>>
            for $crate::hip::Hip<$enc, R>
        {
            /// Copies the value (std's shared pointers cannot be adopted).
            #[inline]
            fn from(value: alloc::rc::Rc<$slice>) -> Self {
                Self::from_inner(&value)
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> From<alloc::sync::Arc<$slice>>
            for $crate::hip::Hip<$enc, R>
        {
            /// Copies the value (std's shared pointers cannot be adopted).
            #[inline]
            fn from(value: alloc::sync::Arc<$slice>) -> Self {
                Self::from_inner(&value)
            }
        }
    };

    // without `From<Box<$slice>>`, for owned types lacking `From<Box<$slice>>`
    ($enc:ty, $slice:ty, $owned:ty, no_box) => {
        impl<'a, R: $crate::repr::Repr<'a>> From<$owned> for $crate::hip::Hip<$enc, R> {
            /// Adopts the buffer when the value does not fit inline (no copy).
            #[inline]
            fn from(value: $owned) -> Self {
                Self::from_owned(value)
            }
        }

        impl<'a, 'o, R: $crate::repr::Repr<'a>> From<&'o $owned> for $crate::hip::Hip<$enc, R> {
            /// Copies the value.
            #[inline]
            fn from(value: &'o $owned) -> Self {
                Self::from_inner(core::borrow::Borrow::<$slice>::borrow(value))
            }
        }

        impl<'a, 's, R: $crate::repr::Repr<'a>> From<&'s mut $slice> for $crate::hip::Hip<$enc, R> {
            /// Copies the value.
            #[inline]
            fn from(value: &'s mut $slice) -> Self {
                Self::from_inner(value)
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> From<$crate::hip::Hip<$enc, R>> for $owned {
            /// O(1) when the value uniquely owns an adopted buffer.
            #[inline]
            fn from(value: $crate::hip::Hip<$enc, R>) -> Self {
                value.into_owned_std()
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> core::borrow::Borrow<$slice>
            for $crate::hip::Hip<$enc, R>
        {
            #[inline]
            fn borrow(&self) -> &$slice {
                self.as_inner()
            }
        }
    };
}

/// Implements the `const` constructors of the borrowing representations.
///
/// `$as_bytes` is a `const`-callable conversion from `&$slice` to `&[u8]`.
macro_rules! impl_borrowed_ctors {
    ($enc:ty, $slice:ty, |$v:ident| $as_bytes:expr) => {
        #[cfg(feature = "hip")]
        $crate::family::impl_borrowed_ctors!(@one Wide, $enc, $slice, |$v| $as_bytes);
        #[cfg(feature = "small")]
        $crate::family::impl_borrowed_ctors!(@one Small, $enc, $slice, |$v| $as_bytes);
    };
    (@one $repr:ident, $enc:ty, $slice:ty, |$v:ident| $as_bytes:expr) => {
        impl<'a, B: $crate::backend::Backend>
            $crate::hip::Hip<$enc, $crate::repr::$repr<'a, B>>
        {
            /// Borrows the value without copying, in a `const` context too.
            #[inline]
            #[must_use]
            pub const fn borrowed($v: &'a $slice) -> Self {
                Self::from_repr_const($crate::repr::$repr::borrowed($as_bytes))
            }

            /// Borrows a static value; alias of `borrowed` kept for clarity.
            #[inline]
            #[must_use]
            pub const fn from_static($v: &'static $slice) -> Self {
                Self::borrowed($v)
            }
        }
    };
}

pub(crate) use impl_borrowed_ctors;
pub(crate) use impl_std_glue;
