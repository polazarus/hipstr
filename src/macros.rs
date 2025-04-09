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

pub(crate) use {symmetric_eq, symmetric_ord};
