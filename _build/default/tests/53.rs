struct S1 {
    u: i32
}

struct S2 {
    x : S1
}

fn f(mut a: S2, mut c: S2) {
    let b : &mut i32 = &mut a.x.u;

    a = c; // BAD : a.x.u is borrowed, not below a deref

    *b = 13i32
}
