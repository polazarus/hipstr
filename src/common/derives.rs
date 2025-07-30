macro_rules! AsRef {
    (
        { target = $dst:ty, method = $method:ident }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* ::core::convert::AsRef<$dst> for $ty where $($generics_where)* {
            #[inline]
            fn as_ref(&self) -> &$dst {
                self.$method()
            }
        }
    }
}

macro_rules! Deref {
    (
        { target = $dst:ty, method = $method:ident }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* ::core::ops::Deref for $ty where $($generics_where)* {
            type Target = $dst;

            #[inline]
            fn deref(&self) -> &$dst {
                self.$method()
            }
        }
    }
}

macro_rules! AsRefAndDeref {
    (
        $($parameters:tt)*
    ) => {
        $crate::common::derives::AsRef! { $($parameters)* }
        $crate::common::derives::Deref! { $($parameters)* }
    }
}

macro_rules! Default {
    (
        { $cons:path }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* ::core::default::Default for $ty where $($generics_where)* {
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
        { bindings = ( $($generics_bindings:tt)* ) $( where ( $($generics_where:tt)* ) )?, source = $source:ty, cons = $cons:path }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        (($ty:ty) ($($_generics_bindings:tt)*)
        where ($($_generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)*
            ::core::convert::From<$source>
        for $ty
        $(where
            $($generics_where)*
        )?
        {
            #[inline]
            fn from(other: $source) -> Self {
                $cons(other)
            }
        }
    };

    (
        { $source:ty, $cons:path }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)*
            ::core::convert::From<$source>
        for $ty
        where
            $($generics_where)*
        {
            #[inline]
            fn from(other: $source) -> Self {
                $cons(other)
            }
        }
    };
}

#[allow(clippy::redundant_pub_crate)]
pub(crate) use {AsRef, AsRefAndDeref, Default, Deref, From};
