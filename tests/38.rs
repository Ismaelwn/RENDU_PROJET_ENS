struct T {
    x : i32,
}

struct S {
    y : T
}

fn f(x : S) -> i32 {
    x.y.x + x.y.x
}
