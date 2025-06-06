fn f() {
    let mut x : i32 = 12i32;
    let mut y : i32 = 12i32;

    let bx : &mut i32 = &mut x;
    let by : &mut i32 = &mut y;
    let bb : & &mut i32 = &bx;

    *bb = by; // BAD: writing to a shared borrow.
}