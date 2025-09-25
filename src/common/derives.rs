#![allow(unused)]

macro_rules! Copy {
    (
        $({
            $(( $(additional_bindings:tt)* ))?
            $(where ($($additional_where:tt)*) )?
        })?
        $_attr:tt
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl<
            $($($generics_bindings)*)?
            $($($(additional_bindings)*)?)?
        > ::core::marker::Copy for $ty
        where $($generics_where)* $($($(additional_where)*)?)?
        {}

        impl<
            $($($generics_bindings)*)?
            $($($(additional_bindings)*)?)?
        > ::core::clone::Clone for $ty
        where $($generics_where)* $($($(additional_where)*)?)? {
            #[inline]
            fn clone(&self) -> Self {
                *self
            }
        }
    };
}

macro_rules! ConstDefault {
    (
        { $value:expr }
        $_attr:tt
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
  ) => {
    impl $(< $($generics_bindings)* >)? ::const_default::ConstDefault for $ty where $($generics_where)* {
        const DEFAULT: Self = $value;
    }
    impl $(< $($generics_bindings)* >)? ::core::default::Default for $ty where $($generics_where)* {
        fn default() -> Self {
            <Self as ::const_default::ConstDefault>::DEFAULT
        }
    }
  };
}

macro_rules! DelegateDebug {
    (
        { $delegate:path $(where $($bound:tt)+ )? }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::fmt::Debug for $ty where $( $($bound)+ ,)? $($generics_where)* {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                $delegate(self).fmt(f)
            }
        }
    };
}

macro_rules! DelegateHash {
    (
        { $delegate:path $(where $($bound:tt)+ )? }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::hash::Hash for $ty where $( $($bound)+ ,)? $($generics_where)* {
            #[inline]
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                $delegate(self).hash(state)
            }
        }
    };
}

macro_rules! AsRef {
    (
        { $as_ty:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::convert::AsRef<$as_ty> for $ty where $($generics_where)* {
            #[inline]
            fn as_ref(&self) -> &$as_ty {
                $delegate(self)
            }
        }
    };
    (
        { $as_ty:ty, $delegate:path, $mut_delegate:path }
        $($rest:tt)*
    ) => {
        $crate::common::derives::AsRef! {
            { $as_ty, $delegate }
            $($rest)*
        }
        $crate::common::derives::AsMut! {
            { $as_ty, $mut_delegate }
            $($rest)*
        }
    };
}

macro_rules! AsMut {
    (
        { $as_ty:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::convert::AsMut<$as_ty> for $ty where $($generics_where)* {
            #[inline]
            fn as_mut(&mut self) -> &mut $as_ty {
                $delegate(self)
            }
        }
    };
}

macro_rules! Borrow {
    (
        { $as_ty:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::borrow::Borrow<$as_ty> for $ty where $($generics_where)* {
            #[inline]
            fn borrow(&self) -> &$as_ty {
                $delegate(self)
            }
        }
    };
    (
        { $as_ty:ty, $delegate:path, $mut_delegate:path }
        $($rest:tt)*
    ) => {
        $crate::common::derives::Borrow! {
            { $as_ty, $delegate }
            $($rest)*
        }
        $crate::common::derives::BorrowMut! {
            { $as_ty, $mut_delegate }
            $($rest)*
        }
    };
}

macro_rules! BorrowMut {
    (
        { $as_ty:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::borrow::BorrowMut<$as_ty> for $ty where $($generics_where)* {
            #[inline]
            fn borrow_mut(&mut self) -> &mut $as_ty {
                $delegate(self)
            }
        }
    };
}

macro_rules! Deref {
    (
        { $target:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::ops::Deref for $ty where $($generics_where)* {
            type Target = $target;

            #[inline]
            fn deref(&self) -> &Self::Target {
                $delegate(self)
            }
        }
    };
    (
        { $target:ty, $delegate:path, $mut_delegate:path }
        $($rest:tt)*
    ) => {
        $crate::common::derives::Deref! {
            { $target, $delegate }
            $($rest)*
        }

        $crate::common::derives::DerefMut! {
            { $target, $mut_delegate }
            $($rest)*
        }
    };
}

macro_rules! DerefMut {
    (
        { $target:ty, $delegate:path }
        ($( ($($_attr:tt)*) )*)
        $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $_body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::ops::DerefMut for $ty where $($generics_where)* {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                $delegate(self)
            }
        }
    };
}

macro_rules! Default {
    (
        { $cons:path }
        $attrs:tt $vis:vis $kind:ident $name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::default::Default for $ty where $($generics_where)* {
            #[inline]
            fn default() -> Self {
                $cons()
            }
        }
    };
    (
        $($parameters:tt)*
    ) => {
        $crate::common::derives::Default! { { Self::new } $($parameters)* }
    };
}

macro_rules! From {
    (
        {
            $source:ty,
            $cons:path
            $(, ( $($additional_bindings:tt)* ) )?
            $(where ( $($additional_where:tt)* ) )?
        }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $body:tt
    ) => {
        impl<
            $($($generics_bindings)*)?
            $($($additional_bindings)*)?
        >
            ::core::convert::From<$source>
        for $ty
        where
            $($generics_where)*
            $($($additional_where)*)?

        {
            #[inline]
            fn from(other: $source) -> Self {
                $cons(other)
            }
        }
    };
}

macro_rules! Into {
    (
        { bindings = $(< ($($generics_bindings:tt)*) >)? $( where ( $($generics_where:tt)* ) )?, target = $target:ty, method = $method:ident }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ($ty:ty)
        $(< ( $($_generics_bindings:tt)* ) >)?
        where ( $($_generics_where:tt)* )
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)?
            ::core::convert::From<$ty>
        for $target
        $(where
            $($generics_where)*
        )?
        {
            #[inline]
            fn from(other: $ty) -> Self {
                other.$method()
            }
        }
    };

    (
        { target = $target:ty, method = $method:ident }
        $attrs:tt $vis:vis $kind:ident $name:ident
        ( $ty:ty )
        $(< ($($generics_bindings:tt)*) >)?
        where ( $($generics_where:tt)* )
        $body:tt
    ) => {
        $crate::common::derives::Into! {
            { bindings = ( $(< $($generics_bindings)* >)? ) where ( $($generics_where)* ), target = $target, method = $method }
            $attrs $vis $kind $name
            (
                ($ty)
                ( $(< $($generics_bindings)* >)? )
                where ( $($generics_where)* )
            )
            $body
        }
    };
}

macro_rules! Vector {
    (
        { $item:ty }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ($ty:ty)
        $(< ($($generics_bindings:tt)*) >)?
        where ($($generics_where:tt)*)
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? $crate::common::traits::sealed::Sealed for $ty where $($generics_where)* {}
        impl $(< $($generics_bindings)* >)? $crate::common::traits::Vector for $ty where $($generics_where)* {
            type Item = $item;
            #[inline]
            fn len(&self) -> usize {
                self.len()
            }
            #[inline]
            fn capacity(&self) -> usize {
                self.capacity()
            }
            #[inline]
            fn as_ptr(&self) -> *const Self::Item {
                self.as_ptr()
            }
            #[inline]
            fn as_slice(&self) -> &[Self::Item] {
                self.as_slice()
            }
        }
    };
}

macro_rules! MutVector {
    (
        { $item:ty }
        $($rest:tt)*
    ) => {
        $crate::common::derives::MutVector! {
            $($rest)*
        }
        $crate::common::derives::Vector! {
            { $item }
            $($rest)*
        }
    };
    (
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ($ty:ty)
        $(< ($($generics_bindings:tt)*) >)?
        where ($($generics_where:tt)*)
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? $crate::common::traits::MutVector for $ty where $($generics_where)* {
            #[inline]
            unsafe fn set_len(&mut self, len: usize) {
                // SAFETY: same safety requirements
                unsafe { self.set_len(len) }
            }
            #[inline]
            fn as_mut_ptr(&mut self) -> *mut Self::Item {
                self.as_mut_ptr()
            }
            #[inline]
            fn as_mut_slice(&mut self) -> &mut [Self::Item] {
                self.as_mut_slice()
            }
            #[inline]
            fn as_non_null(&mut self) -> ::core::ptr::NonNull<Self::Item> {
                self.as_non_null()
            }
        }
    };
}

macro_rules! FromIterator {
    (
        { $item:ty, $cons:path }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ($ty:ty)
        $(< ($($generics_bindings:tt)*) >)?
        where ($($generics_where:tt)*)
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::iter::FromIterator<$item> for $ty where $($generics_where)* {
            #[inline]
            fn from_iter<I: ::core::iter::IntoIterator<Item = $item>>(iterable: I) -> Self {
                $cons(iterable)
            }
        }
    };
}

macro_rules! IntoIterator {
    (
        { $item:ty, $into_iter:path, $cons:path }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        ($ty:ty)
        $(< ($($generics_bindings:tt)*) >)?
        where ($($generics_where:tt)*)
        $body:tt
    ) => {
        impl $(< $($generics_bindings)* >)? ::core::iter::IntoIterator for $ty where $($generics_where)* {
            type Item = $item;
            type IntoIter = $into_iter;

            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                $cons(self)
            }
        }
    };
}

#[allow(clippy::redundant_pub_crate)]
pub(crate) use {
    AsMut, AsRef, Borrow, BorrowMut, ConstDefault, Copy, Default, DelegateDebug, DelegateHash,
    Deref, DerefMut, From, FromIterator, Into, IntoIterator, MutVector, Vector,
};
