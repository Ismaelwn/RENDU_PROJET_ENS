struct S {
    x : i32
}

fn f() -> S {
    S { } // BAD : field x is missing
}