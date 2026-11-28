//! Thread-safety guarantees, checked at compile time.
//!
//! Values with the thread-local `Rc` backend (`Local*` aliases) keep their
//! reference count in a `Cell`: they must be neither `Send` nor `Sync`, or a
//! clone could be sent to another thread and race on the count (the soundness
//! bug fixed in 0.8.1, #54). Each block below must fail to compile:
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalHipStr<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalHipStr<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalSmallStr<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalSmallStr<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalTinyStr>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalTinyStr>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalHipByt<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalHipByt<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalSmallByt<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalSmallByt<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Send>() {}
//! check::<hipstr::LocalTinyByt>();
//! ```
//!
//! ```compile_fail,E0277
//! fn check<T: Sync>() {}
//! check::<hipstr::LocalTinyByt>();
//! ```
//!
//! The thread-safe (`Arc`) and unique backends are `Send` and `Sync` (see the
//! unit test below).

#[cfg(test)]
mod tests {
    use crate::backend::{Arc, Unique};
    use crate::{bytes, string};

    const fn send_sync<T: Send + Sync>() {}

    #[test]
    fn shared_and_unique_backends_are_send_and_sync() {
        send_sync::<string::HipStr<'static, Arc>>();
        send_sync::<string::SmallStr<'static, Arc>>();
        send_sync::<string::TinyStr<Arc>>();
        send_sync::<bytes::HipByt<'static, Arc>>();
        send_sync::<bytes::SmallByt<'static, Arc>>();
        send_sync::<bytes::TinyByt<Arc>>();
        send_sync::<string::HipStr<'static, Unique>>();
        send_sync::<string::SmallStr<'static, Unique>>();
        send_sync::<string::TinyStr<Unique>>();
        send_sync::<bytes::TinyByt<Unique>>();
    }
}
