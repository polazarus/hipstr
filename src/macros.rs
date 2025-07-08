macro_rules! trait_impls {
    () => {};
    ( $( [ $($gen:tt)* ] $(where [ $($wh: tt)* ])? )? { $($body:tt)* } $($rest:tt)*) => {
        $crate::macros::trait_impls!(@@ $( [ $($gen)* ] $( where [ $($wh)* ] )? )? { $($body)* });
        $crate::macros::trait_impls!($($rest)*);
    };
    ( @@ $( [ $($gen:tt)* ] $( where [ $($wh: tt)* ])? )? {} ) => {};
    ( @@ $( [ $($gen:tt)* ] $( where [ $($wh: tt)* ])? )? { $name:ident { $($body:tt)* } $($rest:tt)* } ) => {
        $crate::macros::trait_impls!(@$name $( [ $($gen)* ] $( where [ $($wh)* ] )? )? { $($body)* } );
        $crate::macros::trait_impls!(@@ $( [ $($gen)* ] $( where [ $($wh)* ] )? )? { $($rest)* });
    };

    (@PartialEq $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@PartialEq $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $a:ty; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? core::cmp::PartialEq for $a $($(where $($wh)*)?)? {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                self[..] == other[..]
            }
        }
        $crate::macros::trait_impls!(@PartialEq $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };
    (@PartialEq $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $a:ty, $b:ty; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? core::cmp::PartialEq<$b> for $a $($(where $($wh)*)?)? {
            #[inline]
            fn eq(&self, other: &$b) -> bool {
                self[..] == other[..]
            }
        }
        $crate::macros::trait_impls!(@PartialEq $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@PartialOrd $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@PartialOrd $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $a:ty ; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? core::cmp::PartialOrd for $a $($(where $($wh)*)?)? {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                self[..].partial_cmp(&other[..])
            }
        }
        $crate::macros::trait_impls!(@PartialOrd $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };
    (@PartialOrd $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $a:ty, $b:ty ; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? core::cmp::PartialOrd<$b> for $a $($(where $($wh)*)?)? {
            #[inline]
            fn partial_cmp(&self, other: &$b) -> Option<core::cmp::Ordering> {
                self[..].partial_cmp(&other[..])
            }
        }
        $crate::macros::trait_impls!(@PartialOrd $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@From $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@From $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $b:ty => $a:ty = $cons:path; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? From<$b> for $a $($(where $($wh)*)?)? {
            #[inline]
            fn from(other: $b) -> Self {
                $cons(other)
            }
        }
        $crate::macros::trait_impls!(@From $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@FromIterator $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@FromIterator $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $el:ty => $t:ty = $f:path; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? FromIterator<$el> for $t $($(where $($wh)*)?)? {
            fn from_iter<T001: IntoIterator<Item = $el>>(iter: T001) -> Self {
                $f(iter)
            }
        }
        $crate::macros::trait_impls!(@FromIterator $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@Debug $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@Debug $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $t:ty ; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? core::fmt::Debug for $t $($(where $($wh)*)?)? {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let slice: &[_] = self;
                slice.fmt(f)
            }
        }
        $crate::macros::trait_impls!(@Debug $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@Vector $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@Vector $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $t:ty : $item:ty ; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? crate::common::traits::sealed::Sealed for $t $(where $($wh)*)? {}
        impl $(< $($gen)* >)? crate::common::traits::Vector for $t $(where $($wh)*)? {
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
        $crate::macros::trait_impls!(@Vector $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@MutVector $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@MutVector $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $t:ty ; $($rest:tt)* }) => {
        unsafe impl $(< $($gen)* >)? crate::common::traits::MutVector for $t $($(where $($wh)*)?)? {
            #[inline]
            unsafe fn set_len(&mut self, len: usize) {
                unsafe { self.set_len(len) }
            }
            #[inline]
            fn as_non_null(&mut self) -> core::ptr::NonNull<Self::Item> {
                self.as_non_null()
            }
        }
        $crate::macros::trait_impls!(@MutVector $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };

    (@Extend $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { }) => {};
    (@Extend $([ $($gen:tt)* ] $( where [ $($wh:tt)* ])? )? { $el:ty => $t:ty ; $($rest:tt)* }) => {
        impl $(< $($gen)* >)? Extend<$el> for $t $($(where $($wh)*)?)? {
            fn extend<T001: IntoIterator<Item = $el>>(&mut self, iter: T001) {
                self.extend_iter(iter)
            }
        }
        $crate::macros::trait_impls!(@Extend $([ $($gen)* ] $( where [ $($wh)* ])? )? { $($rest)* });
    };
}

macro_rules! symmetric_eq {
    () => {};

    ($([ $($gen:tt)* ])? $([ where $($wh:tt)* ])? ($a:ty, $b:ty) = $f:path ; $($($other:tt)+)?) => {
        impl $(< $($gen)* >)? core::cmp::PartialEq<$a> for $b where $($($wh)*)? {
            #[inline]
            fn eq(&self, other: &$a) -> bool {
                $f(other, self)
            }
        }

        impl $(< $($gen)* >)? core::cmp::PartialEq<$b> for $a where $($($wh)*)? {
            #[inline]
            fn eq(&self, other: &$b) -> bool {
                $f(self, other)
            }
        }

        $( $crate::macros::symmetric_eq!( $($other)* ); )?
    };

}

macro_rules! symmetric_ord {
    () => {};

    ( $( [ $( $gen:tt )* ] )? $( [ where $($wh:tt)* ] )? ($a_typ:ty, $b_typ:ty) = $f:path ; $($($other:tt)+)? ) => {
        impl $(< $($gen)* >)? core::cmp::PartialOrd < $a_typ > for $b_typ $(where $($wh)*)?
        {
            #[inline]
            fn partial_cmp(&self, other: & $a_typ) -> Option<core::cmp::Ordering> {
                $f(other, self).map(core::cmp::Ordering::reverse)
            }
        }

        impl $(< $($gen)* >)? core::cmp::PartialOrd < $b_typ > for $a_typ $(where $($wh)*)?
        {
            #[inline]
            fn partial_cmp(&self, other: & $b_typ) -> Option<core::cmp::Ordering> {
                $f(self, other)
            }
        }

        $( $crate::macros::symmetric_ord!( $($other)* ); )?
    }
}

pub(crate) use {symmetric_eq, symmetric_ord, trait_impls};
