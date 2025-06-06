struct Box {}

struct S {
    x : Box,
    y : Box
}

fn f() -> S {
    loop {}
}

fn use_box(b: Box) {}
fn use_s(b: S) {}


fn g() {
    let mut x : S = f();

    use_box(x.x);
    x.x = Box {}; // We reinitialize x.x
    use_s(x);
}
