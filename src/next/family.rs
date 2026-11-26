//! Glue generated once per encoding family.
//!
//! Generic impls cover most traits (see [`hip`](super::hip)); what remains
//! are impls whose `Self` type is a std type, which coherence forbids writing
//! generically over the encoding.

/// Implements conversions and comparisons with the std borrowed and owned
/// forms of an encoding, in both directions.
macro_rules! impl_std_glue {
    ($enc:ty, $slice:ty, $owned:ty) => {
        impl<'a, R: $crate::next::repr::Repr<'a, u8>> From<$owned> for $crate::next::hip::Hip<$enc, R> {
            /// Adopts the buffer when the value does not fit inline (no copy).
            #[inline]
            fn from(value: $owned) -> Self {
                Self::from_owned(value)
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> From<$crate::next::hip::Hip<$enc, R>> for $owned {
            /// O(1) when the value uniquely owns an adopted buffer.
            #[inline]
            fn from(value: $crate::next::hip::Hip<$enc, R>) -> Self {
                value.into_owned_std()
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> From<alloc::boxed::Box<$slice>>
            for $crate::next::hip::Hip<$enc, R>
        {
            #[inline]
            fn from(value: alloc::boxed::Box<$slice>) -> Self {
                Self::from_owned(<$owned>::from(value))
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> core::borrow::Borrow<$slice>
            for $crate::next::hip::Hip<$enc, R>
        {
            #[inline]
            fn borrow(&self) -> &$slice {
                self.as_inner()
            }
        }

        $crate::next::family::impl_std_glue!(@eq $enc, $slice);
        $crate::next::family::impl_std_glue!(@eq $enc, &$slice);
        $crate::next::family::impl_std_glue!(@eq $enc, $owned);
    };

    (@eq $enc:ty, $other:ty) => {
        impl<'a, R: $crate::next::repr::Repr<'a, u8>> PartialEq<$other> for $crate::next::hip::Hip<$enc, R> {
            #[inline]
            fn eq(&self, other: &$other) -> bool {
                let other: &<$enc as $crate::next::enc::Encoding>::Slice = other.as_ref();
                self.as_inner() == other
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> PartialEq<$crate::next::hip::Hip<$enc, R>> for $other {
            #[inline]
            fn eq(&self, other: &$crate::next::hip::Hip<$enc, R>) -> bool {
                let this: &<$enc as $crate::next::enc::Encoding>::Slice = self.as_ref();
                this == other.as_inner()
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> PartialOrd<$other> for $crate::next::hip::Hip<$enc, R> {
            #[inline]
            fn partial_cmp(&self, other: &$other) -> Option<core::cmp::Ordering> {
                let other: &<$enc as $crate::next::enc::Encoding>::Slice = other.as_ref();
                self.as_inner().partial_cmp(other)
            }
        }

        impl<'a, R: $crate::next::repr::Repr<'a, u8>> PartialOrd<$crate::next::hip::Hip<$enc, R>> for $other {
            #[inline]
            fn partial_cmp(&self, other: &$crate::next::hip::Hip<$enc, R>) -> Option<core::cmp::Ordering> {
                let this: &<$enc as $crate::next::enc::Encoding>::Slice = self.as_ref();
                this.partial_cmp(other.as_inner())
            }
        }
    };
}

/// Implements the `const` constructors of the borrowing representations.
///
/// `$as_bytes` is a `const`-callable conversion from `&$slice` to `&[u8]`.
macro_rules! impl_borrowed_ctors {
    ($enc:ty, $slice:ty, |$v:ident| $as_bytes:expr) => {
        $crate::next::family::impl_borrowed_ctors!(@one Wide, $enc, $slice, |$v| $as_bytes);
        $crate::next::family::impl_borrowed_ctors!(@one Small, $enc, $slice, |$v| $as_bytes);
    };
    (@one $repr:ident, $enc:ty, $slice:ty, |$v:ident| $as_bytes:expr) => {
        impl<'a, B: $crate::next::backend::Backend>
            $crate::next::hip::Hip<$enc, $crate::next::repr::$repr<'a, u8, B>>
        {
            /// Borrows the value without copying, in a `const` context too.
            #[inline]
            #[must_use]
            pub const fn borrowed($v: &'a $slice) -> Self {
                Self::from_repr_const($crate::next::repr::$repr::borrowed($as_bytes))
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
