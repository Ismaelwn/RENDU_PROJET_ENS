struct Box { }

struct S {
    x : i32,
    y : Box
}

fn f() -> S {
    loop {}
}

fn use_i32(x: i32) {}
fn use_s(x: S) {}

fn g() {
    let x : S = f();

    use_i32(x.x);
    use_i32(x.x);
    use_s(x);
}
