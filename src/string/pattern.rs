#![allow(clippy::module_name_repetitions)]

use alloc::string::String;

use super::HipStr;
use crate::backend::Backend;

pub trait Adopt<'borrow, B>
where
    B: Backend,
{
    type Output;
    unsafe fn adopt_unchecked(self, source: &HipStr<'borrow, B>) -> Self::Output;
}

impl<'borrow, B: Backend> Adopt<'borrow, B> for &str {
    type Output = HipStr<'borrow, B>;
    #[inline]
    unsafe fn adopt_unchecked(self, source: &HipStr<'borrow, B>) -> Self::Output {
        unsafe { source.slice_ref_unchecked(self) }
    }
}

impl<'borrow, B: Backend> Adopt<'borrow, B> for (usize, &str) {
    type Output = (usize, HipStr<'borrow, B>);
    #[inline]
    unsafe fn adopt_unchecked(self, source: &HipStr<'borrow, B>) -> Self::Output {
        (self.0, unsafe { source.slice_ref_unchecked(self.1) })
    }
}

#[must_use]
pub struct IterWrapper<'haystack, 'borrow, B, I>
where
    B: Backend,
{
    source: &'haystack HipStr<'borrow, B>,
    inner: I,
}

impl<B, I: Clone> Clone for IterWrapper<'_, '_, B, I>
where
    B: Backend,
{
    fn clone(&self) -> Self {
        Self {
            source: self.source,
            inner: self.inner.clone(),
        }
    }
}

impl<'haystack, 'borrow, B, I> IterWrapper<'haystack, 'borrow, B, I>
where
    B: Backend,
{
    pub(crate) const fn new(source: &'haystack HipStr<'borrow, B>, inner: I) -> Self {
        Self { source, inner }
    }
}

impl<'borrow, B, S> Iterator for IterWrapper<'_, 'borrow, B, S>
where
    B: Backend,
    S: Iterator,
    S::Item: Adopt<'borrow, B>,
{
    type Item = <S::Item as Adopt<'borrow, B>>::Output;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|item| unsafe { item.adopt_unchecked(self.source) })
    }
}

impl<'borrow, B, S> DoubleEndedIterator for IterWrapper<'_, 'borrow, B, S>
where
    B: Backend,
    S: Iterator + DoubleEndedIterator,
    S::Item: Adopt<'borrow, B>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|item| unsafe { item.adopt_unchecked(self.source) })
    }
}

pub trait Pattern: Sized {
    type Split<'a>;
    fn split(self, haystack: &str) -> Self::Split<'_>;

    type SplitInclusive<'a>;
    fn split_inclusive(self, haystack: &str) -> Self::SplitInclusive<'_>;

    type SplitTerminator<'a>;
    fn split_terminator(self, haystack: &str) -> Self::SplitTerminator<'_>;

    type SplitN<'a>;
    fn splitn(self, n: usize, haystack: &str) -> Self::SplitN<'_>;
    fn split_once(self, haystack: &str) -> Option<(&str, &str)>;

    type Matches<'a>;
    fn matches(self, haystack: &str) -> Self::Matches<'_>;

    type MatchIndices<'a>;
    fn match_indices(self, haystack: &str) -> Self::MatchIndices<'_>;

    fn trim_start_matches(self, s: &str) -> &str;

    fn strip_prefix(self, haystack: &str) -> Option<&str>;
}

pub trait ReversePattern: Pattern {
    fn strip_suffix(self, haystack: &str) -> Option<&str>;

    fn trim_end_matches(self, haystack: &str) -> &str;

    type RSplit<'a>;
    fn rsplit(self, haystack: &str) -> Self::RSplit<'_>;

    type RSplitTerminator<'a>;
    fn rsplit_terminator(self, haystack: &str) -> Self::RSplitTerminator<'_>;

    type RSplitN<'a>;
    fn rsplitn(self, n: usize, haystack: &str) -> Self::RSplitN<'_>;

    fn rsplit_once(self, haystack: &str) -> Option<(&str, &str)>;

    type RMatches<'a>;
    fn rmatches(self, haystack: &str) -> Self::RMatches<'_>;

    type RMatchIndices<'a>;
    fn rmatch_indices(self, haystack: &str) -> Self::RMatchIndices<'_>;
}

pub trait DoubleEndedPattern: ReversePattern {
    fn trim_matches(self, s: &str) -> &str;
}

macro_rules! impl_pat {
    (reverse $( < $( $gl:lifetime ),* $(,)? > <$($gt:ident),* $(,)?> <$(const $gc:ident: $gct:ty),* $(,)?> )? for $t:ty $(where $($w:tt)*)?) => {
        impl_pat!(
            $( < $( $gl ),* > < $( $gt ),* > <$(const  $gc : $gct ),* > )?
            for $t $(where $($w)* )?
        );

        impl$(<$($gl,)* $($gt,)* $( const $gc: $gct, )* >)? ReversePattern for $t $(where $($w)*)? {
            fn strip_suffix(self, haystack: &str) -> Option<&str>{
                haystack.strip_suffix(self)
            }

            fn trim_end_matches(self, haystack: &str) -> &str {
                haystack.trim_end_matches(self)
            }

            type RSplit<'haystack> = core::str::RSplit<'haystack, Self>;
            #[inline]
            fn rsplit(self, haystack: &str) -> Self::RSplit<'_> {
                haystack.rsplit(self)
            }

            type RSplitTerminator<'haystack> = core::str::RSplitTerminator<'haystack, Self>;
            #[inline]
            fn rsplit_terminator(self, haystack: &str) -> Self::RSplitTerminator<'_> {
                haystack.rsplit_terminator(self)
            }

            type RSplitN<'haystack> = core::str::RSplitN<'haystack, Self>;
            #[inline]
            fn rsplitn(self, n:usize, haystack: &str) -> Self::RSplitN<'_> {
                haystack.rsplitn(n, self)
            }

            #[inline]
            fn rsplit_once(self, haystack: &str) -> Option<(&str, &str)> {
                haystack.rsplit_once(self)
            }

            type RMatches<'haystack> = core::str::RMatches<'haystack, Self>;
            #[inline]
            fn rmatches(self, haystack: &str) -> Self::RMatches<'_> {
                haystack.rmatches(self)
            }

            type RMatchIndices<'haystack> = core::str::RMatchIndices<'haystack, Self>;
            #[inline]
            fn rmatch_indices(self, haystack: &str) -> Self::RMatchIndices<'_> {
                haystack.rmatch_indices(self)
            }

        }
    };
    (double_ended $( < $( $gl:lifetime ),* $(,)? > <$($gt:ident),* $(,)?> <$(const $gc:ident: $gct:ty),* $(,)?> )? for $t:ty $(where $($w:tt)*)?) => {
        impl_pat!(reverse
            $( < $( $gl ),* > < $( $gt ),* > <$(const  $gc : $gct ),* > )?
            for $t $(where $($w)* )?
        );

        impl$(<$($gl,)* $($gt,)* $( const $gc: $gct, )* >)? DoubleEndedPattern for $t $(where $($w)*)? {
            fn trim_matches(self, haystack: &str) -> &str {
                haystack.trim_matches(self)
            }
        }
    };
    ($( < $( $gl:lifetime ),* $(,)? > <$($gt:ident),* $(,)?> <$(const $gc:ident: $gct:ty),* $(,)?> )? for $t:ty $(where $($w:tt)*)?) => {
        impl$(<$($gl,)* $($gt,)* $( const $gc: $gct, )* >)? Pattern for $t $(where $($w)*)? {
            type Split<'haystack> = core::str::Split<'haystack, Self>;
            #[inline]
            fn split(self, haystack: &str) -> Self::Split<'_> {
                haystack.split(self)
            }

            type SplitInclusive<'haystack> = core::str::SplitInclusive<'haystack, Self>;
            #[inline]
            fn split_inclusive(self, haystack: &str) -> Self::SplitInclusive<'_> {
                haystack.split_inclusive(self)
            }

            type SplitTerminator<'haystack> = core::str::SplitTerminator<'haystack, Self>;
            #[inline]
            fn split_terminator(self, haystack: &str) -> Self::SplitTerminator<'_> {
                haystack.split_terminator(self)
            }
            type SplitN<'haystack> = core::str::SplitN<'haystack, Self>;
            #[inline]
            fn splitn(self, n:usize, haystack: &str) -> Self::SplitN<'_> {
                haystack.splitn(n, self)
            }

            #[inline]
            fn split_once(self, haystack: &str) -> Option<(&str, &str)> {
                haystack.split_once(self)
            }
            type Matches<'haystack> = core::str::Matches<'haystack, Self>;
            #[inline]
            fn matches(self, haystack: &str) -> Self::Matches<'_> {
                haystack.matches(self)
            }

            type MatchIndices<'haystack> = core::str::MatchIndices<'haystack, Self>;
            #[inline]
            fn match_indices(self, haystack: &str) -> Self::MatchIndices<'_> {
                haystack.match_indices(self)
            }

            #[inline]
            fn trim_start_matches(self, haystack: &str) -> &str {
                haystack.trim_start_matches(self)
            }


            #[inline]
            fn strip_prefix(self, haystack: &str) -> Option<&str> {
                haystack.strip_prefix(self)
            }
        }
    };
}

impl_pat!(reverse <'a> <> <> for &'a str);
impl_pat!(reverse <'a, 'b> <> <> for &'a &'b str);
impl_pat!(reverse <'a> <> <> for &'a String);
impl_pat!(double_ended for char);
impl_pat!(double_ended <'a> <> <> for &'a [char]);
impl_pat!(double_ended <'a> <F> <> for F where F: (FnMut(char) -> bool) + Sized);
impl_pat!(reverse <'a> <> <const N: usize> for &'a [char; N]);
