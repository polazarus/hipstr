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

macro_rules! AsMut {
    (
        { target = $dst:ty, method = $method:ident }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* ::core::convert::AsMut<$dst> for $ty where $($generics_where)* {
            #[inline]
            fn as_mut(&mut self) -> &mut $dst {
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

macro_rules! DerefMut {
    (
        { method = $method:ident }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* ::core::ops::DerefMut for $ty where $($generics_where)* {
            #[inline]
            fn deref_mut(&mut self) -> &mut <Self as ::core::ops::Deref>::Target {
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

macro_rules! AsRefAsMutDerefDerefMut {
    (
        {target= $dst:ty, method = $method:ident, method_mut = $method_mut:ident}
        $($rest:tt)*
    ) => {
        $crate::common::derives::AsRef! { { target = $dst, method = $method } $($rest)* }
        $crate::common::derives::Deref! { { target = $dst, method = $method } $($rest)* }
        $crate::common::derives::AsMut! { { target = $dst, method = $method_mut } $($rest)* }
        $crate::common::derives::DerefMut! { { method = $method_mut } $($rest)* }

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
        (
            ($ty:ty)
            ( $($_generics_bindings:tt)* )
            where ( $($_generics_where:tt)* )
        )
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
        { source = $source:ty, cons = $cons:path }
        $attrs:tt $vis:vis $kind:ident $name:ident
        (
            ( $ty:ty )
            ( $($generics_bindings:tt)* )
            where ( $($generics_where:tt)* )
        )
        $body:tt
    ) => {
        $crate::common::derives::From! {
            { bindings = ( $($generics_bindings)* ) where ( $($generics_where)* ), source = $source, cons = $cons }
            $attrs $vis $kind $name
            (
                ($ty)
                ( $($generics_bindings)* )
                where ( $($generics_where)* )
            )
            $body
        }
    };
}

macro_rules! Into {
    (
        { bindings = ( $($generics_bindings:tt)* ) $( where ( $($generics_where:tt)* ) )?, target = $target:ty, method = $method:ident }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        (
            ($ty:ty)
            ( $($_generics_bindings:tt)* )
            where ( $($_generics_where:tt)* )
        )
        $body:tt
    ) => {
        impl $($generics_bindings)*
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
        (
            ( $ty:ty )
            ( $($generics_bindings:tt)* )
            where ( $($generics_where:tt)* )
        )
        $body:tt
    ) => {
        $crate::common::derives::Into! {
            { bindings = ( $($generics_bindings)* ) where ( $($generics_where)* ), target = $target, method = $method }
            $attrs $vis $kind $name
            (
                ($ty)
                ( $($generics_bindings)* )
                where ( $($generics_where)* )
            )
            $body
        }
    };
}

macro_rules! Vector {
    (
        { item = $item:ty }
        $_attrs:tt $_vis:vis $_kind:ident $_name:ident
        (($ty:ty) ($($generics_bindings:tt)*)
        where ($($generics_where:tt)*))
        $body:tt
    ) => {
        impl $($generics_bindings)* $crate::common::traits::sealed::Sealed for $ty where $($generics_where)* {}
        impl $($generics_bindings)* $crate::common::traits::Vector for $ty where $($generics_where)* {
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
        }
    };
}

#[allow(clippy::redundant_pub_crate)]
pub(crate) use {
    AsMut, AsRef, AsRefAndDeref, AsRefAsMutDerefDerefMut, Default, Deref, DerefMut, From, Into,
    Vector,
};
