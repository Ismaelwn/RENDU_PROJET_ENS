// BAD : duplicated lifetime variable name
fn f<'a, 'a>(mut x: &'a i32) {}
