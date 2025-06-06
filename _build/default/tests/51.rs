fn f<'a>(mut a: &'a mut i32, c: &'a mut i32) {
    let b : &mut i32 = &mut * a;

    a = c; // Allowed even though a subplace of a is borrowed, because the existing
           // borrow of a is below a deref

    *a = 12i32; // And the borrow of *a is now inactive.

    *b = 13i32
}
