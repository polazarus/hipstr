#[test]
#[cfg(feature = "unstable")]
fn test() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/bad_backend/too_large.rs");
    t.compile_fail("tests/bad_backend/align_req.rs");
}
