struct S1 {
    u: i32
}

struct S2<'a> {
    x : &'a mut S1
}

fn f<'a>(mut a: S2<'a>, c: S2<'a>) {
    let b : &mut i32 = &mut (* a.x).u;

    a = c; // Allowed even though a subplace of a is borrowed, because the existing
           // borrow of a is below a deref

    (*a.x).u = 12i32; // And the borrow is now inactive.

    *b = 13i32
}
