struct S1 {
    u: i32
}

struct S2<'a> {
    x : &'a mut S1
}

fn f<'a>(a: S2<'a>) {
    let b : &mut i32 = &mut (* a.x).u;

    *a.x = S1{u : 1i32}; // BAD: a.x is borrowed

    *b = 13i32
}
