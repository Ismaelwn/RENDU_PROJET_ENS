struct B<'a> {
    f: &'a mut i32
}

fn f<'a>(mut a: B<'a>, c: B<'a>) {
    let b : B = B { f: &mut * a.f };

    a = B { f: c.f }; // Allowed even though a subplace of a is borrowed, because the existing
                      // borrow of a is below a deref

    *a.f = 12i32; // And the borrow of *a is now inactive.

    *b.f = 13i32
}
