use crate::traits::MutVector;

#[track_caller]
pub fn pointer_stability<T: Copy + Default>(v: &mut impl MutVector<Item = T>) {
    let p = v.as_ptr();
    let len = v.len();
    let cap = v.capacity();
    for i in len..cap {
        v.push(T::default());
        assert_eq!(p, v.as_ptr(), "pointer has changed after push: {i}/{cap}");
    }
}
