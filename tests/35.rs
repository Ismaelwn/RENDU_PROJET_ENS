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

    use_s(x);
    x.x = Box {}; // BAD : x has been consumed, so we cannot write to one of its fields
}
