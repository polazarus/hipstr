macro_rules! symmetric_eq {
    () => {};
    ($(< $($gen_l:lifetime),* $(,)?> <$($gen_t:ident),* $(,)?> < $(const $gen_c:ident : $gen_ct:ty),* $(,)?> $([where $($wh:tt)* ])? )? ($a_var:ident : $a_typ:ty, $b_var:ident : $b_typ:ty) { $($e:tt)* } $($($other:tt)+)? ) => {
        impl $(< $( $gen_l, )* $( $gen_t, )* $(const $gen_c : $gen_ct, )* >)? core::cmp::PartialEq < $a_typ > for $b_typ $($(where $($wh)*)?)?
        {
            #[inline]
            fn eq(&self, other: & $a_typ) -> bool {
                let $b_var = self;
                let $a_var = other;
                $($e)*
            }
        }

        impl $(< $( $gen_l, )* $( $gen_t, )* $( const $gen_c : $gen_ct, )* >)? core::cmp::PartialEq < $b_typ > for $a_typ $($(where $($wh)*)?)?
        {
            #[inline]
            fn eq(&self, other: & $b_typ) -> bool {
                let $a_var = self;
                let $b_var = other;
                $($e)*
            }
        }

        $( $crate::macros::symmetric_eq!( $($other)* ); )?
    }
}

macro_rules! symmetric_ord {
    () => {};
    ($(< $($gen_l:lifetime),* $(,)?> <$($gen_t:ident),* $(,)?> < $(const $gen_c:ident : $gen_ct:ty),* $(,)?> $([where $($wh:tt)* ])? )? ($a_var:ident : $a_typ:ty, $b_var:ident : $b_typ:ty) { $($e:tt)* } $($($other:tt)+)? ) => {
        impl $(< $($gen_l ,)* $($gen_t, )* $( const $gen_c : $gen_ct, )*>)? core::cmp::PartialOrd < $a_typ > for $b_typ $($(where $($wh)*)?)?
        {
            #[inline]
            fn partial_cmp(&self, other: & $a_typ) -> Option<core::cmp::Ordering> {
                let $b_var = self;
                let $a_var = other;
                let result = { $($e)* };
                result.map(core::cmp::Ordering::reverse)
            }
        }

        impl $(< $( $gen_l, )* $( $gen_t, )* $( const $gen_c : $gen_ct, )*>)? core::cmp::PartialOrd < $b_typ > for $a_typ $($(where $($wh)*)?)?
        {
            #[inline]
            fn partial_cmp(&self, other: & $b_typ) -> Option<core::cmp::Ordering> {
                let $a_var = self;
                let $b_var = other;
                let result = { $($e)* };
                result
            }
        }

        $( $crate::macros::symmetric_ord!( $($other)* ); )?
    }
}

pub(crate) use {symmetric_eq, symmetric_ord};
