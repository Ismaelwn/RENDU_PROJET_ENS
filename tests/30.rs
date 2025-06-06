struct Box {}

struct S {
    x : Box,
    y : Box
}

fn f() -> S {
    loop {}
}

fn use_box(b: Box) {}

fn g() {
    let mut x : S;
    let mut y : S;

    x = f();
    y = x;

    x = f();

    use_box(x.x);
    use_box(x.y);
    use_box(y.x);
    use_box(y.y);
}
