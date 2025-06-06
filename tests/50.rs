fn f() {
    let mut x : i32 = 42i32;
    let mut y : i32 = 42i32;

    let mut b : &mut i32 = &mut x;

    b = &mut y; // Deactivate borrow of x.

    x = 12i32;

    *b = 13i32;
}
