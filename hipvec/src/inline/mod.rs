use layouts::BasicLayout;

mod base;
pub mod copy;
pub mod layouts;
pub mod noncopy;

pub type InlineVec<T> = noncopy::InlineVec<T, BasicLayout>;
pub type CopyInlineVec<T> = copy::InlineVec<T, BasicLayout>;

// TODO improve repetitions to use from iterator when available

/// Creates an [`InlineVec`] containing the arguments.
///
/// `inline_vec!` allows `InlineVec`s to be defined with the same syntax as array expressions. There
/// are two forms of this macro:
///
/// - Create an [`InlineVec`] containing a given list of elements:
///
/// ```
/// let v = inline_vec![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// ```
///
/// - Create an [`InlineVec`] from a given element and size:
///
/// ```
/// let v = inline_vec![1; 3];
/// assert_eq!(v, [1, 1, 1]);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements which implement [`Clone`]
/// and the number of elements doesn't have to be a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful using this with types
/// having a nonstandard `Clone` implementation. For example, `inline_vec![Rc::new(1); 2]` will
/// create an inline vector of two references to the same boxed integer value, not two references
/// pointing to independently boxed integers.
///
/// Also, note that `inline_vec![expr; 0]` is allowed, and produces an empty inline vector. This
/// will still evaluate `expr`, however, and immediately drop the resulting value, so be mindful of
/// side effects.
///
/// [`InlineVec`]: crate::inline::InlineVec
#[macro_export]
macro_rules! inline_vec {
    () => {
        $crate::inline::InlineVec::new()
    };
    ($e:expr; $n:expr) => {
        {
            let mut vec = $crate::inline::InlineVec::with_capacity($n);
            for e in core::iter::repeat_n($e, $n) {
                vec.push(e);
            }
            vec
        }
    };
    ($($e:expr),* $(,)?) => {
        {
            let mut vec = $crate::inline::InlineVec::with_capacity($crate::__count!($($e),*));
            $(
                vec.push($e);
            )*
            vec
        }
    };
}

/// Creates a [`CopyInlineVec`] containing the arguments.
///
/// `copy_inline_vec!` allows `CopyInlineVec`s to be defined with the same syntax as array
/// expressions. There are two forms of this macro:
///
/// - Create a [`CopyInlineVec`] containing a given list of elements:
///
/// ```
/// let v = copy_inline_vec![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// ```
///
/// - Create a [`CopyInlineVec`] from a given element and size:
///
/// ```
/// let v = copy_inline_vec![1; 3];
/// assert_eq!(v, [1, 1, 1]);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements which implement [`Clone`]
/// and the number of elements doesn't have to be a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful using this with types
/// having a nonstandard `Clone` implementation. For example, `copy_inline_vec![Rc::new(1); 2]` will
/// create a inline vector of two references to the same boxed integer value, not two references
/// pointing to independently boxed integers.
///
/// Also, note that `copy_inline_vec![expr; 0]` is allowed, and produces an empty inline vector.
/// This will still evaluate `expr`, however, and immediately drop the resulting value, so be
/// mindful of side effects.
///
/// [`CopyInlineVec`]: crate::inline::CopyInlineVec
#[macro_export]
macro_rules! copy_inline_vec {
    () => {
        $crate::inline::CopyInlineVec::new()
    };
    ($e:expr; $n:expr) => {
        {
            let mut vec = $crate::inline::CopyInlineVec::with_capacity($n);
            for e in core::iter::repeat_n($e, $n) {
                vec.push(e);
            }
            vec
        }
    };
    ($($e:expr),* $(,)?) => {
        {
            let mut vec = $crate::inline::CopyInlineVec::with_capacity($crate::__count!($($e),*));
            $(
                vec.push($e);
            )*
            vec
        }
    };
}
