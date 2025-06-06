fn f() {
    let mut x : i32 = 12i32;
    let mut y : i32 = 13i32;
    let mut b : &mut i32 = &mut x;
    let mut r : i32 = 0i32;

    loop {
        r = y + 1i32; // BAD : y is borrowed at the previous iteration

        r = r + *b; // b is live, hence the borrow of *y* is active


        b = &mut y;
    }
}