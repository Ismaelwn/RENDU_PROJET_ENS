struct S {
    a: i32,
    b: i32,
}

fn f() -> i32 {
    let x: S;
    x.a // BAD : x is uninitialized
}
