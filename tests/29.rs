struct S<'a> {
    x: i32,
    y: &'a mut i32
}

fn f<'a>(mut x: &'a mut i32) -> S<'a> {
    // BAD : x is moved to field y, and *then* dereferenced to write to field x
    S { y: x, x: *x }
}
